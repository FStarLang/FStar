open Prims
let cases :
  'Auu____11 'Auu____12 .
    ('Auu____11 -> 'Auu____12) ->
      'Auu____12 -> 'Auu____11 FStar_Pervasives_Native.option -> 'Auu____12
  =
  fun f  ->
    fun d  ->
      fun uu___252_32  ->
        match uu___252_32 with
        | FStar_Pervasives_Native.Some x -> f x
        | FStar_Pervasives_Native.None  -> d
  
type closure =
  | Clos of
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
     FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term,
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
     FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple2 FStar_Syntax_Syntax.memo,Prims.bool)
  FStar_Pervasives_Native.tuple4 
  | Univ of FStar_Syntax_Syntax.universe 
  | Dummy 
let (uu___is_Clos : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____124 -> false
  
let (__proj__Clos__item___0 :
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
       FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term,
      ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
         FStar_Pervasives_Native.tuple2 Prims.list,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 FStar_Syntax_Syntax.memo,Prims.bool)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Clos _0 -> _0 
let (uu___is_Univ : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____228 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____241 -> false
  
type env =
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list
let (dummy :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2)
  = (FStar_Pervasives_Native.None, Dummy) 
type branches =
  (FStar_Syntax_Syntax.pat,FStar_Syntax_Syntax.term
                             FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.tuple3 Prims.list
type stack_elt =
  | Arg of (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
  FStar_Pervasives_Native.tuple3 
  | UnivArgs of (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
  FStar_Pervasives_Native.tuple2 
  | MemoLazy of (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
  FStar_Syntax_Syntax.memo 
  | Match of (env,branches,FStar_TypeChecker_Cfg.cfg,FStar_Range.range)
  FStar_Pervasives_Native.tuple4 
  | Abs of
  (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                         FStar_Pervasives_Native.option,
  FStar_Range.range) FStar_Pervasives_Native.tuple5 
  | App of
  (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
  FStar_Pervasives_Native.tuple4 
  | Meta of (env,FStar_Syntax_Syntax.metadata,FStar_Range.range)
  FStar_Pervasives_Native.tuple3 
  | Let of
  (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
  FStar_Pervasives_Native.tuple4 
  | Cfg of FStar_TypeChecker_Cfg.cfg 
  | Debug of (FStar_Syntax_Syntax.term,FStar_Util.time)
  FStar_Pervasives_Native.tuple2 
let (uu___is_Arg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____415 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____453 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____491 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____564 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,FStar_TypeChecker_Cfg.cfg,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____614 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____672 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____716 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____756 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____794 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> FStar_TypeChecker_Cfg.cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____812 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____839 = FStar_Syntax_Util.head_and_args' t  in
    match uu____839 with | (hd1,uu____855) -> hd1
  
let mk :
  'Auu____882 .
    'Auu____882 ->
      FStar_Range.range -> 'Auu____882 FStar_Syntax_Syntax.syntax
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
          let uu____945 = FStar_ST.op_Bang r  in
          match uu____945 with
          | FStar_Pervasives_Native.Some uu____993 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____1065 =
      FStar_List.map
        (fun uu____1079  ->
           match uu____1079 with
           | (bopt,c) ->
               let uu____1092 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____1094 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____1092 uu____1094) env
       in
    FStar_All.pipe_right uu____1065 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___253_1097  ->
    match uu___253_1097 with
    | Clos (env,t,uu____1100,uu____1101) ->
        let uu____1146 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____1153 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____1146 uu____1153
    | Univ uu____1154 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___254_1159  ->
    match uu___254_1159 with
    | Arg (c,uu____1161,uu____1162) ->
        let uu____1163 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____1163
    | MemoLazy uu____1164 -> "MemoLazy"
    | Abs (uu____1171,bs,uu____1173,uu____1174,uu____1175) ->
        let uu____1180 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____1180
    | UnivArgs uu____1187 -> "UnivArgs"
    | Match uu____1194 -> "Match"
    | App (uu____1203,t,uu____1205,uu____1206) ->
        let uu____1207 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____1207
    | Meta (uu____1208,m,uu____1210) -> "Meta"
    | Let uu____1211 -> "Let"
    | Cfg uu____1220 -> "Cfg"
    | Debug (t,uu____1222) ->
        let uu____1223 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____1223
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____1233 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____1233 (FStar_String.concat "; ")
  
let is_empty : 'Auu____1242 . 'Auu____1242 Prims.list -> Prims.bool =
  fun uu___255_1249  ->
    match uu___255_1249 with | [] -> true | uu____1252 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        (fun uu___274_1283  ->
           match () with
           | () ->
               let uu____1284 =
                 FStar_List.nth env x.FStar_Syntax_Syntax.index  in
               FStar_Pervasives_Native.snd uu____1284) ()
      with
      | uu___273_1301 ->
          let uu____1302 =
            let uu____1303 = FStar_Syntax_Print.db_to_string x  in
            let uu____1304 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____1303
              uu____1304
             in
          failwith uu____1302
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____1312 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____1312
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____1316 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____1316
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____1320 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____1320
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
          let uu____1354 =
            FStar_List.fold_left
              (fun uu____1380  ->
                 fun u1  ->
                   match uu____1380 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1405 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____1405 with
                        | (k_u,n1) ->
                            let uu____1420 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____1420
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____1354 with
          | (uu____1438,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 (fun uu___276_1463  ->
                    match () with
                    | () ->
                        let uu____1466 =
                          let uu____1467 = FStar_List.nth env x  in
                          FStar_Pervasives_Native.snd uu____1467  in
                        (match uu____1466 with
                         | Univ u3 ->
                             ((let uu____1486 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      cfg.FStar_TypeChecker_Cfg.tcenv)
                                   (FStar_Options.Other "univ_norm")
                                  in
                               if uu____1486
                               then
                                 let uu____1487 =
                                   FStar_Syntax_Print.univ_to_string u3  in
                                 FStar_Util.print1
                                   "Univ (in norm_universe): %s\n" uu____1487
                               else ());
                              aux u3)
                         | Dummy  -> [u2]
                         | uu____1489 ->
                             let uu____1490 =
                               let uu____1491 = FStar_Util.string_of_int x
                                  in
                               FStar_Util.format1
                                 "Impossible: universe variable u@%s bound to a term"
                                 uu____1491
                                in
                             failwith uu____1490)) ()
               with
               | uu____1499 ->
                   if
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else
                     (let uu____1503 =
                        let uu____1504 = FStar_Util.string_of_int x  in
                        Prims.strcat "Universe variable not found: u@"
                          uu____1504
                         in
                      failwith uu____1503))
          | FStar_Syntax_Syntax.U_unif uu____1507 when
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1516 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1525 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1532 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____1532 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____1549 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____1549 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1557 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1565 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____1565 with
                                  | (uu____1570,m) -> n1 <= m))
                           in
                        if uu____1557 then rest1 else us1
                    | uu____1575 -> us1)
               | uu____1580 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1584 = aux u3  in
              FStar_List.map (fun _0_16  -> FStar_Syntax_Syntax.U_succ _0_16)
                uu____1584
           in
        if
          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1588 = aux u  in
           match uu____1588 with
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
            (fun uu____1756  ->
               let uu____1757 = FStar_Syntax_Print.tag_of_term t  in
               let uu____1758 = env_to_string env  in
               let uu____1759 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____1757 uu____1758 uu____1759);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____1768 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____1771 ->
                    let uu____1794 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____1794
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____1795 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____1796 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____1797 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____1798 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____1822 ->
                           let uu____1835 =
                             let uu____1836 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____1837 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____1836 uu____1837
                              in
                           failwith uu____1835
                       | uu____1840 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___256_1875  ->
                                         match uu___256_1875 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____1882 =
                                               let uu____1889 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____1889)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____1882
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___277_1899 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___277_1899.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___277_1899.FStar_Syntax_Syntax.sort)
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
                                              | uu____1904 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____1907 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___278_1911 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___278_1911.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___278_1911.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____1932 =
                        let uu____1933 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____1933  in
                      mk uu____1932 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____1941 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1941  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____1943 = lookup_bvar env x  in
                    (match uu____1943 with
                     | Univ uu____1946 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___279_1950 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___279_1950.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___279_1950.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____1956,uu____1957) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____2046  ->
                              fun stack1  ->
                                match uu____2046 with
                                | (a,aq) ->
                                    let uu____2058 =
                                      let uu____2059 =
                                        let uu____2066 =
                                          let uu____2067 =
                                            let uu____2098 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____2098, false)  in
                                          Clos uu____2067  in
                                        (uu____2066, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____2059  in
                                    uu____2058 :: stack1) args)
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
                    let uu____2286 = close_binders cfg env bs  in
                    (match uu____2286 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____2341 =
                      let uu____2354 =
                        let uu____2363 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____2363]  in
                      close_binders cfg env uu____2354  in
                    (match uu____2341 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____2408 =
                             let uu____2409 =
                               let uu____2416 =
                                 let uu____2417 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____2417
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____2416, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____2409  in
                           mk uu____2408 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____2516 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____2516
                      | FStar_Util.Inr c ->
                          let uu____2530 = close_comp cfg env c  in
                          FStar_Util.Inr uu____2530
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____2549 =
                        let uu____2550 =
                          let uu____2577 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____2577, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____2550  in
                      mk uu____2549 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____2623 =
                            let uu____2624 =
                              let uu____2631 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____2631, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____2624  in
                          mk uu____2623 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____2683  -> dummy :: env1) env
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
                    let uu____2704 =
                      let uu____2715 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____2715
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____2734 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___280_2750 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___280_2750.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___280_2750.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____2734))
                       in
                    (match uu____2704 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___281_2768 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___281_2768.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___281_2768.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___281_2768.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___281_2768.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____2782,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____2845  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____2862 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____2862
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____2874  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____2898 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____2898
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___282_2906 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___282_2906.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___282_2906.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___283_2907 = lb  in
                      let uu____2908 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___283_2907.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___283_2907.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____2908;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___283_2907.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___283_2907.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____2940  -> fun env1  -> dummy :: env1)
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
            (fun uu____3029  ->
               let uu____3030 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3031 = env_to_string env  in
               let uu____3032 = stack_to_string stack  in
               let uu____3033 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____3030 uu____3031 uu____3032 uu____3033);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____3038,uu____3039),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____3118 = close_binders cfg env' bs  in
               (match uu____3118 with
                | (bs1,uu____3134) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____3154 =
                      let uu___284_3157 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___284_3157.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___284_3157.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____3154)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____3213 =
                 match uu____3213 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____3328 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____3357 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____3441  ->
                                     fun uu____3442  ->
                                       match (uu____3441, uu____3442) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____3581 = norm_pat env4 p1
                                              in
                                           (match uu____3581 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____3357 with
                            | (pats1,env4) ->
                                ((let uu___285_3743 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___285_3743.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___286_3762 = x  in
                             let uu____3763 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___286_3762.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___286_3762.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3763
                             }  in
                           ((let uu___287_3777 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___287_3777.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___288_3788 = x  in
                             let uu____3789 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___288_3788.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___288_3788.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3789
                             }  in
                           ((let uu___289_3803 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___289_3803.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___290_3819 = x  in
                             let uu____3820 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___290_3819.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___290_3819.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3820
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___291_3837 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___291_3837.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____3842 = norm_pat env2 pat  in
                     (match uu____3842 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____3911 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____3911
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____3930 =
                   let uu____3931 =
                     let uu____3954 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____3954)  in
                   FStar_Syntax_Syntax.Tm_match uu____3931  in
                 mk uu____3930 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____4069 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____4178  ->
                                       match uu____4178 with
                                       | (a,q) ->
                                           let uu____4205 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____4205, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____4069
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____4218 =
                       let uu____4225 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____4225)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____4218
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____4237 =
                       let uu____4246 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____4246)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____4237
                 | uu____4251 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____4257 -> failwith "Impossible: unexpected stack element")

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
            let uu____4272 =
              let uu____4273 = inline_closure_env cfg env [] t  in
              FStar_Syntax_Syntax.Meta uu____4273  in
            FStar_Pervasives_Native.Some uu____4272
        | i -> i

and (close_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                   FStar_Pervasives_Native.option)
           FStar_Pervasives_Native.tuple2 Prims.list,env)
          FStar_Pervasives_Native.tuple2)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____4290 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4374  ->
                  fun uu____4375  ->
                    match (uu____4374, uu____4375) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___292_4515 = b  in
                          let uu____4516 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___292_4515.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___292_4515.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4516
                          }  in
                        let imp1 = close_imp cfg env1 imp  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp1) :: out))) (env, []))
           in
        match uu____4290 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____4656 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4669 = inline_closure_env cfg env [] t  in
                 let uu____4670 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____4669 uu____4670
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4683 = inline_closure_env cfg env [] t  in
                 let uu____4684 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4683 uu____4684
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____4738  ->
                           match uu____4738 with
                           | (a,q) ->
                               let uu____4759 =
                                 inline_closure_env cfg env [] a  in
                               (uu____4759, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___257_4776  ->
                           match uu___257_4776 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4780 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____4780
                           | f -> f))
                    in
                 let uu____4784 =
                   let uu___293_4785 = c1  in
                   let uu____4786 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4786;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___293_4785.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____4784)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___258_4796  ->
            match uu___258_4796 with
            | FStar_Syntax_Syntax.DECREASES uu____4797 -> false
            | uu____4800 -> true))

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
            let flags1 =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___259_4818  ->
                      match uu___259_4818 with
                      | FStar_Syntax_Syntax.DECREASES uu____4819 -> false
                      | uu____4822 -> true))
               in
            let rc1 =
              let uu___294_4824 = rc  in
              let uu____4825 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___294_4824.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4825;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____4834 -> lopt

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
    let uu____4901 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____4901 with
    | FStar_Pervasives_Native.Some e ->
        let uu____4940 = FStar_Syntax_Embeddings.unembed e t  in
        uu____4940 true FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____4960 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____4960) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____5022  ->
           fun subst1  ->
             match uu____5022 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____5063,uu____5064)) ->
                      let uu____5123 = b  in
                      (match uu____5123 with
                       | (bv,uu____5131) ->
                           let uu____5132 =
                             let uu____5133 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____5133  in
                           if uu____5132
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____5138 = unembed_binder term1  in
                              match uu____5138 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____5145 =
                                      let uu___295_5146 = bv  in
                                      let uu____5147 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___295_5146.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___295_5146.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____5147
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____5145
                                     in
                                  let b_for_x =
                                    let uu____5153 =
                                      let uu____5160 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____5160)
                                       in
                                    FStar_Syntax_Syntax.NT uu____5153  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___260_5176  ->
                                         match uu___260_5176 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____5177,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____5179;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____5180;_})
                                             ->
                                             let uu____5185 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____5185
                                         | uu____5186 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____5187 -> subst1)) env []
  
let reduce_primops :
  'Auu____5209 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv,'Auu____5209) FStar_Pervasives_Native.tuple2
           FStar_Pervasives_Native.option,closure)
          FStar_Pervasives_Native.tuple2 Prims.list ->
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
            (let uu____5261 = FStar_Syntax_Util.head_and_args tm  in
             match uu____5261 with
             | (head1,args) ->
                 let uu____5306 =
                   let uu____5307 = FStar_Syntax_Util.un_uinst head1  in
                   uu____5307.FStar_Syntax_Syntax.n  in
                 (match uu____5306 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____5313 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                      (match uu____5313 with
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
                                (fun uu____5341  ->
                                   let uu____5342 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name
                                      in
                                   let uu____5343 =
                                     FStar_Util.string_of_int l  in
                                   let uu____5350 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____5342 uu____5343 uu____5350);
                              tm)
                           else
                             (let uu____5352 =
                                if l = prim_step.FStar_TypeChecker_Cfg.arity
                                then (args, [])
                                else
                                  FStar_List.splitAt
                                    prim_step.FStar_TypeChecker_Cfg.arity
                                    args
                                 in
                              match uu____5352 with
                              | (args_1,args_2) ->
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____5439  ->
                                        let uu____5440 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____5440);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____5443  ->
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
                                           (fun uu____5457  ->
                                              let uu____5458 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____5458);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5464  ->
                                              let uu____5465 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____5466 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____5465 uu____5466);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____5467 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____5471  ->
                                 let uu____5472 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____5472);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5476  ->
                            let uu____5477 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5477);
                       (match args with
                        | (a1,uu____5481)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____5506 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5520  ->
                            let uu____5521 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5521);
                       (match args with
                        | (t,uu____5525)::(r,uu____5527)::[] ->
                            let uu____5568 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____5568 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____5574 -> tm))
                  | uu____5585 -> tm))
  
let reduce_equality :
  'Auu____5596 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv,'Auu____5596) FStar_Pervasives_Native.tuple2
           FStar_Pervasives_Native.option,closure)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun tm  ->
        reduce_primops norm_cb
          (let uu___296_5649 = cfg  in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___297_5652 = FStar_TypeChecker_Cfg.default_steps  in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___297_5652.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___297_5652.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___297_5652.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___297_5652.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___297_5652.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___297_5652.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___297_5652.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___297_5652.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___297_5652.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___297_5652.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___297_5652.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___297_5652.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___297_5652.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___297_5652.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___297_5652.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___297_5652.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___297_5652.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___297_5652.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___297_5652.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___297_5652.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___297_5652.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___297_5652.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___297_5652.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___297_5652.FStar_TypeChecker_Cfg.nbe_step)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___296_5649.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___296_5649.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___296_5649.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___296_5649.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___296_5649.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___296_5649.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___296_5649.FStar_TypeChecker_Cfg.reifying)
           }) tm
  
type norm_request_t =
  | Norm_request_none 
  | Norm_request_ready 
  | Norm_request_requires_rejig 
let (uu___is_Norm_request_none : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_none  -> true | uu____5658 -> false
  
let (uu___is_Norm_request_ready : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_ready  -> true | uu____5664 -> false
  
let (uu___is_Norm_request_requires_rejig : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Norm_request_requires_rejig  -> true
    | uu____5670 -> false
  
let (is_norm_request :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.args -> norm_request_t) =
  fun hd1  ->
    fun args  ->
      let aux min_args =
        let uu____5687 = FStar_All.pipe_right args FStar_List.length  in
        FStar_All.pipe_right uu____5687
          (fun n1  ->
             if n1 < min_args
             then Norm_request_none
             else
               if n1 = min_args
               then Norm_request_ready
               else Norm_request_requires_rejig)
         in
      let uu____5710 =
        let uu____5711 = FStar_Syntax_Util.un_uinst hd1  in
        uu____5711.FStar_Syntax_Syntax.n  in
      match uu____5710 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          -> aux (Prims.parse_int "2")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          aux (Prims.parse_int "1")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          aux (Prims.parse_int "3")
      | uu____5717 -> Norm_request_none
  
let (should_consider_norm_requests : FStar_TypeChecker_Cfg.cfg -> Prims.bool)
  =
  fun cfg  ->
    (Prims.op_Negation
       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
      &&
      (let uu____5724 =
         FStar_Ident.lid_equals
           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
           FStar_Parser_Const.prims_lid
          in
       Prims.op_Negation uu____5724)
  
let (rejig_norm_request :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term)
  =
  fun hd1  ->
    fun args  ->
      let uu____5735 =
        let uu____5736 = FStar_Syntax_Util.un_uinst hd1  in
        uu____5736.FStar_Syntax_Syntax.n  in
      match uu____5735 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          ->
          (match args with
           | t1::t2::rest when
               (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____5793 = FStar_Syntax_Util.mk_app hd1 [t1; t2]  in
               FStar_Syntax_Util.mk_app uu____5793 rest
           | uu____5820 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize_term")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          (match args with
           | t::rest when (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____5858 = FStar_Syntax_Util.mk_app hd1 [t]  in
               FStar_Syntax_Util.mk_app uu____5858 rest
           | uu____5877 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          (match args with
           | t1::t2::t3::rest when
               (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____5949 = FStar_Syntax_Util.mk_app hd1 [t1; t2; t3]  in
               FStar_Syntax_Util.mk_app uu____5949 rest
           | uu____5984 ->
               failwith "Impossible! invalid rejig_norm_request for norm")
      | uu____5985 ->
          let uu____5986 =
            let uu____5987 = FStar_Syntax_Print.term_to_string hd1  in
            Prims.strcat "Impossible! invalid rejig_norm_request for: %s"
              uu____5987
             in
          failwith uu____5986
  
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s  ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
  
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___261_6003  ->
    match uu___261_6003 with
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
        let uu____6009 =
          let uu____6012 =
            let uu____6013 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldOnly uu____6013  in
          [uu____6012]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6009
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____6019 =
          let uu____6022 =
            let uu____6023 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldFully uu____6023  in
          [uu____6022]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6019
    | FStar_Syntax_Embeddings.UnfoldAttr names1 ->
        let uu____6029 =
          let uu____6032 =
            let uu____6033 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldAttr uu____6033  in
          [uu____6032]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6029
    | FStar_Syntax_Embeddings.NBE  -> [FStar_TypeChecker_Env.NBE]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  = fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____6055 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term,'Auu____6055)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____6106 =
            let uu____6111 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____6111 s  in
          match uu____6106 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____6127 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____6127
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
        let inherited_steps =
          FStar_List.append
            (if
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
             then [FStar_TypeChecker_Env.EraseUniverses]
             else [])
            (if
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
             then [FStar_TypeChecker_Env.AllowUnboundUniverses]
             else [])
           in
        match args with
        | uu____6153::(tm,uu____6155)::[] ->
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
        | (tm,uu____6184)::[] ->
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
        | (steps,uu____6205)::uu____6206::(tm,uu____6208)::[] ->
            let add_exclude s z =
              let uu____6246 =
                FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s  in
              if uu____6246
              then s
              else (FStar_TypeChecker_Env.Exclude z) :: s  in
            let uu____6250 =
              let uu____6255 = full_norm steps  in parse_steps uu____6255  in
            (match uu____6250 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = FStar_TypeChecker_Env.Beta :: s  in
                 let s2 = add_exclude s1 FStar_TypeChecker_Env.Zeta  in
                 let s3 = add_exclude s2 FStar_TypeChecker_Env.Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____6294 -> FStar_Pervasives_Native.None
  
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun s  ->
      fun tm  ->
        let delta_level =
          let uu____6325 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___262_6330  ->
                    match uu___262_6330 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____6331 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____6332 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____6335 -> true
                    | uu____6338 -> false))
             in
          if uu____6325
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta]  in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____6345  ->
             let uu____6346 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____6346);
        (let tm_norm =
           let uu____6348 =
             let uu____6363 = FStar_TypeChecker_Cfg.cfg_env cfg  in
             uu____6363.FStar_TypeChecker_Env.nbe  in
           uu____6348 s cfg.FStar_TypeChecker_Cfg.tcenv tm  in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____6367  ->
              let uu____6368 = FStar_Syntax_Print.term_to_string tm_norm  in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____6368);
         tm_norm)
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___263_6375  ->
    match uu___263_6375 with
    | (App
        (uu____6378,{
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reify );
                      FStar_Syntax_Syntax.pos = uu____6379;
                      FStar_Syntax_Syntax.vars = uu____6380;_},uu____6381,uu____6382))::uu____6383
        -> true
    | uu____6388 -> false
  
let firstn :
  'Auu____6397 .
    Prims.int ->
      'Auu____6397 Prims.list ->
        ('Auu____6397 Prims.list,'Auu____6397 Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack  ->
      let rec drop_irrel uu___264_6448 =
        match uu___264_6448 with
        | (MemoLazy uu____6453)::s -> drop_irrel s
        | (UnivArgs uu____6463)::s -> drop_irrel s
        | s -> s  in
      let uu____6476 = drop_irrel stack  in
      match uu____6476 with
      | (App
          (uu____6479,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____6480;
                        FStar_Syntax_Syntax.vars = uu____6481;_},uu____6482,uu____6483))::uu____6484
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____6489 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____6512) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____6522) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____6543  ->
                  match uu____6543 with
                  | (a,uu____6553) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6563 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____6586 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____6587 -> false
    | FStar_Syntax_Syntax.Tm_type uu____6600 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____6601 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____6602 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____6603 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____6604 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____6605 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____6612 -> false
    | FStar_Syntax_Syntax.Tm_let uu____6619 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____6632 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____6651 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____6666 -> true
    | FStar_Syntax_Syntax.Tm_match uu____6673 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____6743  ->
                   match uu____6743 with
                   | (a,uu____6753) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____6764) ->
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
            | FStar_Syntax_Syntax.Meta_pattern args ->
                FStar_Util.for_some
                  (FStar_Util.for_some
                     (fun uu____6892  ->
                        match uu____6892 with
                        | (a,uu____6902) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____6911,uu____6912,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____6918,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____6924 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____6931 -> false
            | FStar_Syntax_Syntax.Meta_named uu____6932 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____6938 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____6944 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_fully  -> true | uu____6950 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_reify  -> true | uu____6956 -> false
  
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
            let uu____6985 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
            match uu____6985 with
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
              (fun uu____7113  ->
                 fun uu____7114  ->
                   match (uu____7113, uu____7114) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____7174 =
            match uu____7174 with
            | (x,y,z) ->
                let uu____7184 = FStar_Util.string_of_bool x  in
                let uu____7185 = FStar_Util.string_of_bool y  in
                let uu____7186 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____7184 uu____7185
                  uu____7186
             in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg  in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____7205  ->
                    let uu____7206 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____7207 = FStar_Util.string_of_bool b  in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____7206 uu____7207);
               if b then reif else no)
            else
              if
                (let uu____7215 = FStar_TypeChecker_Cfg.find_prim_step cfg fv
                    in
                 FStar_Option.isSome uu____7215)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7220  ->
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
                          ((is_rec,uu____7254),uu____7255);
                        FStar_Syntax_Syntax.sigrng = uu____7256;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7258;
                        FStar_Syntax_Syntax.sigattrs = uu____7259;_},uu____7260),uu____7261),uu____7262,uu____7263,uu____7264)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7369  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____7370,uu____7371,uu____7372,uu____7373) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7440  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____7442),uu____7443);
                        FStar_Syntax_Syntax.sigrng = uu____7444;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7446;
                        FStar_Syntax_Syntax.sigattrs = uu____7447;_},uu____7448),uu____7449),uu____7450,uu____7451,uu____7452)
                     when
                     is_rec &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7557  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____7558,FStar_Pervasives_Native.Some
                    uu____7559,uu____7560,uu____7561) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7629  ->
                           let uu____7630 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____7630);
                      (let uu____7631 =
                         let uu____7640 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____7660 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____7660
                            in
                         let uu____7667 =
                           let uu____7676 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____7696 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____7696
                              in
                           let uu____7707 =
                             let uu____7716 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____7736 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____7736
                                in
                             [uu____7716]  in
                           uu____7676 :: uu____7707  in
                         uu____7640 :: uu____7667  in
                       comb_or uu____7631))
                 | (uu____7767,uu____7768,FStar_Pervasives_Native.Some
                    uu____7769,uu____7770) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7838  ->
                           let uu____7839 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____7839);
                      (let uu____7840 =
                         let uu____7849 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____7869 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____7869
                            in
                         let uu____7876 =
                           let uu____7885 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____7905 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____7905
                              in
                           let uu____7916 =
                             let uu____7925 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____7945 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____7945
                                in
                             [uu____7925]  in
                           uu____7885 :: uu____7916  in
                         uu____7849 :: uu____7876  in
                       comb_or uu____7840))
                 | (uu____7976,uu____7977,uu____7978,FStar_Pervasives_Native.Some
                    uu____7979) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8047  ->
                           let uu____8048 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8048);
                      (let uu____8049 =
                         let uu____8058 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8078 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8078
                            in
                         let uu____8085 =
                           let uu____8094 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8114 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8114
                              in
                           let uu____8125 =
                             let uu____8134 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8154 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8154
                                in
                             [uu____8134]  in
                           uu____8094 :: uu____8125  in
                         uu____8058 :: uu____8085  in
                       comb_or uu____8049))
                 | uu____8185 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8231  ->
                           let uu____8232 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____8233 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____8234 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level
                              in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____8232 uu____8233 uu____8234);
                      (let uu____8235 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___265_8239  ->
                                 match uu___265_8239 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.InliningDelta  ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____8241 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv
                                        in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____8241 l))
                          in
                       FStar_All.pipe_left yesno uu____8235)))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____8253  ->
               let uu____8254 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____8255 =
                 let uu____8256 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____8256  in
               let uu____8257 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____8254 uu____8255 uu____8257);
          (match res with
           | (false ,uu____8258,uu____8259) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____8260 ->
               let uu____8267 =
                 let uu____8268 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____8268
                  in
               FStar_All.pipe_left failwith uu____8267)
  
let decide_unfolding :
  'Auu____8283 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'Auu____8283 ->
            FStar_Syntax_Syntax.fv ->
              FStar_TypeChecker_Env.qninfo ->
                (FStar_TypeChecker_Cfg.cfg,stack_elt Prims.list)
                  FStar_Pervasives_Native.tuple2
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
                    let uu___298_8352 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___299_8355 = cfg.FStar_TypeChecker_Cfg.steps
                            in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___299_8355.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___299_8355.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___299_8355.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___299_8355.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___299_8355.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___299_8355.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___299_8355.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___299_8355.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___299_8355.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___299_8355.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___299_8355.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___299_8355.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___299_8355.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___299_8355.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___299_8355.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___299_8355.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___299_8355.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___299_8355.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___299_8355.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___299_8355.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___299_8355.FStar_TypeChecker_Cfg.nbe_step)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___298_8352.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___298_8352.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___298_8352.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___298_8352.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___298_8352.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___298_8352.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___298_8352.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___298_8352.FStar_TypeChecker_Cfg.reifying)
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
                    | (UnivArgs us)::t ->
                        let uu____8418 = push1 e t  in (UnivArgs us) ::
                          uu____8418
                    | h::t -> e :: h :: t  in
                  let ref =
                    let uu____8428 =
                      let uu____8435 =
                        let uu____8436 =
                          let uu____8437 = FStar_Syntax_Syntax.lid_of_fv fv
                             in
                          FStar_Const.Const_reflect uu____8437  in
                        FStar_Syntax_Syntax.Tm_constant uu____8436  in
                      FStar_Syntax_Syntax.mk uu____8435  in
                    uu____8428 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let stack1 =
                    push1
                      (App
                         (env, ref, FStar_Pervasives_Native.None,
                           FStar_Range.dummyRange)) stack
                     in
                  FStar_Pervasives_Native.Some (cfg, stack1)
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____8728 ->
                   let uu____8751 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____8751
               | uu____8752 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____8761  ->
               let uu____8762 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____8763 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____8764 = FStar_Syntax_Print.term_to_string t1  in
               let uu____8765 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____8772 =
                 let uu____8773 =
                   let uu____8776 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8776
                    in
                 stack_to_string uu____8773  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____8762 uu____8763 uu____8764 uu____8765 uu____8772);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____8802  ->
               let uu____8803 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____8803);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8807  ->
                     let uu____8808 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8808);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____8809 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8813  ->
                     let uu____8814 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8814);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____8815 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8819  ->
                     let uu____8820 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8820);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____8821 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8825  ->
                     let uu____8826 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8826);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8827;
                 FStar_Syntax_Syntax.fv_delta = uu____8828;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8832  ->
                     let uu____8833 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8833);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8834;
                 FStar_Syntax_Syntax.fv_delta = uu____8835;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____8836);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8846  ->
                     let uu____8847 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8847);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid
                  in
               let uu____8851 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
               (match uu____8851 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level _0_17) when
                    _0_17 = (Prims.parse_int "0") ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____8857  ->
                          let uu____8858 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____8858);
                     rebuild cfg env stack t1)
                | uu____8859 ->
                    let uu____8862 =
                      decide_unfolding cfg env stack
                        t1.FStar_Syntax_Syntax.pos fv qninfo
                       in
                    (match uu____8862 with
                     | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                         do_unfold_fv cfg1 env stack1 t1 qninfo fv
                     | FStar_Pervasives_Native.None  ->
                         rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_quoted uu____8889 ->
               let uu____8896 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____8896
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____8924 = is_norm_request hd1 args  in
                  uu____8924 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu____8927 = rejig_norm_request hd1 args  in
                 norm cfg env stack uu____8927))
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____8955 = is_norm_request hd1 args  in
                  uu____8955 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___300_8959 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___301_8962 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___301_8962.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___301_8962.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___301_8962.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___301_8962.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___301_8962.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___301_8962.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___301_8962.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___301_8962.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___301_8962.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___301_8962.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___301_8962.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___301_8962.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___301_8962.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___301_8962.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___301_8962.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___301_8962.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___301_8962.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___301_8962.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___301_8962.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___301_8962.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___301_8962.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___301_8962.FStar_TypeChecker_Cfg.nbe_step)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___300_8959.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___300_8959.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___300_8959.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___300_8959.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___300_8959.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___300_8959.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____8967 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____8967 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____9000  ->
                                 fun stack1  ->
                                   match uu____9000 with
                                   | (a,aq) ->
                                       let uu____9012 =
                                         let uu____9013 =
                                           let uu____9020 =
                                             let uu____9021 =
                                               let uu____9052 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____9052, false)
                                                in
                                             Clos uu____9021  in
                                           (uu____9020, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____9013  in
                                       uu____9012 :: stack1) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____9140  ->
                            let uu____9141 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____9141);
                       norm cfg env stack1 hd1))
                 | FStar_Pervasives_Native.Some (s,tm) when is_nbe_request s
                     ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____9163 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting NBE request on %s ... \n" uu____9163)
                      else ();
                      (let tm' = closure_as_term cfg env tm  in
                       let start = FStar_Util.now ()  in
                       let tm_norm = nbe_eval cfg s tm'  in
                       let fin = FStar_Util.now ()  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         (let uu____9170 =
                            let uu____9171 =
                              let uu____9172 = FStar_Util.time_diff start fin
                                 in
                              FStar_Pervasives_Native.snd uu____9172  in
                            FStar_Util.string_of_int uu____9171  in
                          let uu____9177 =
                            FStar_Syntax_Print.term_to_string tm'  in
                          let uu____9178 =
                            FStar_Syntax_Print.term_to_string tm_norm  in
                          FStar_Util.print3 "NBE'd (%s ms) %s\n\tto %s\n"
                            uu____9170 uu____9177 uu____9178)
                       else ();
                       norm cfg env stack tm_norm))
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____9193 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting norm request on %s ... \n" uu____9193)
                      else ();
                      (let delta_level =
                         let uu____9198 =
                           FStar_All.pipe_right s
                             (FStar_Util.for_some
                                (fun uu___266_9203  ->
                                   match uu___266_9203 with
                                   | FStar_TypeChecker_Env.UnfoldUntil
                                       uu____9204 -> true
                                   | FStar_TypeChecker_Env.UnfoldOnly
                                       uu____9205 -> true
                                   | FStar_TypeChecker_Env.UnfoldFully
                                       uu____9208 -> true
                                   | uu____9211 -> false))
                            in
                         if uu____9198
                         then
                           [FStar_TypeChecker_Env.Unfold
                              FStar_Syntax_Syntax.delta_constant]
                         else [FStar_TypeChecker_Env.NoDelta]  in
                       let cfg'1 =
                         let uu___302_9216 = cfg  in
                         let uu____9217 =
                           let uu___303_9218 =
                             FStar_TypeChecker_Cfg.to_fsteps s  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___303_9218.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___303_9218.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___303_9218.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak =
                               (uu___303_9218.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___303_9218.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___303_9218.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___303_9218.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___303_9218.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               (uu___303_9218.FStar_TypeChecker_Cfg.unfold_only);
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___303_9218.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___303_9218.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___303_9218.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___303_9218.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___303_9218.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___303_9218.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___303_9218.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___303_9218.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___303_9218.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___303_9218.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___303_9218.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___303_9218.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___303_9218.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               true;
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___303_9218.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___303_9218.FStar_TypeChecker_Cfg.nbe_step)
                           }  in
                         {
                           FStar_TypeChecker_Cfg.steps = uu____9217;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___302_9216.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___302_9216.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = delta_level;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___302_9216.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong =
                             (uu___302_9216.FStar_TypeChecker_Cfg.strong);
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___302_9216.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___302_9216.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let stack' =
                         let tail1 = (Cfg cfg) :: stack  in
                         if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           let uu____9223 =
                             let uu____9224 =
                               let uu____9229 = FStar_Util.now ()  in
                               (t1, uu____9229)  in
                             Debug uu____9224  in
                           uu____9223 :: tail1
                         else tail1  in
                       norm cfg'1 env stack' tm))))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____9233 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____9233
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____9242 =
                      let uu____9249 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____9249, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____9242  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____9258 = lookup_bvar env x  in
               (match uu____9258 with
                | Univ uu____9259 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                    then
                      let uu____9308 = FStar_ST.op_Bang r  in
                      (match uu____9308 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9426  ->
                                 let uu____9427 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____9428 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____9427
                                   uu____9428);
                            (let uu____9429 = maybe_weakly_reduced t'  in
                             if uu____9429
                             then
                               match stack with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____9430 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____9505)::uu____9506 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____9516,uu____9517))::stack_rest ->
                    (match c with
                     | Univ uu____9521 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____9530 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____9559  ->
                                    let uu____9560 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____9560);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____9594  ->
                                    let uu____9595 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____9595);
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
                       (fun uu____9663  ->
                          let uu____9664 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____9664);
                     norm cfg env stack1 t1)
                | (Match uu____9665)::uu____9666 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9679 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9679 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9715  -> dummy :: env1) env)
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
                                          let uu____9758 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9758)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___304_9765 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___304_9765.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___304_9765.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9766 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9772  ->
                                 let uu____9773 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9773);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___305_9784 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___305_9784.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___305_9784.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___305_9784.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___305_9784.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___305_9784.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___305_9784.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___305_9784.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___305_9784.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____9787)::uu____9788 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9797 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9797 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9833  -> dummy :: env1) env)
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
                                          let uu____9876 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9876)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___304_9883 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___304_9883.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___304_9883.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9884 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9890  ->
                                 let uu____9891 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9891);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___305_9902 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___305_9902.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___305_9902.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___305_9902.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___305_9902.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___305_9902.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___305_9902.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___305_9902.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___305_9902.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____9905)::uu____9906 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9917 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9917 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9953  -> dummy :: env1) env)
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
                                          let uu____9996 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9996)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___304_10003 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___304_10003.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___304_10003.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10004 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10010  ->
                                 let uu____10011 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10011);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___305_10022 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___305_10022.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___305_10022.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___305_10022.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___305_10022.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___305_10022.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___305_10022.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___305_10022.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___305_10022.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____10025)::uu____10026 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10039 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10039 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10075  -> dummy :: env1) env)
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
                                          let uu____10118 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10118)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___304_10125 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___304_10125.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___304_10125.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10126 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10132  ->
                                 let uu____10133 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10133);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___305_10144 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___305_10144.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___305_10144.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___305_10144.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___305_10144.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___305_10144.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___305_10144.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___305_10144.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___305_10144.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____10147)::uu____10148 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10161 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10161 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10197  -> dummy :: env1) env)
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
                                          let uu____10240 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10240)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___304_10247 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___304_10247.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___304_10247.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10248 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10254  ->
                                 let uu____10255 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10255);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___305_10266 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___305_10266.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___305_10266.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___305_10266.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___305_10266.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___305_10266.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___305_10266.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___305_10266.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___305_10266.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____10269)::uu____10270 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10287 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10287 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10323  -> dummy :: env1) env)
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
                                          let uu____10366 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10366)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___304_10373 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___304_10373.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___304_10373.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10374 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10380  ->
                                 let uu____10381 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10381);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___305_10392 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___305_10392.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___305_10392.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___305_10392.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___305_10392.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___305_10392.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___305_10392.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___305_10392.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___305_10392.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____10397 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10397 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10433  -> dummy :: env1) env)
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
                                          let uu____10476 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10476)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___304_10483 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___304_10483.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___304_10483.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10484 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10490  ->
                                 let uu____10491 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10491);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___305_10502 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___305_10502.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___305_10502.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___305_10502.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___305_10502.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___305_10502.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___305_10502.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___305_10502.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___305_10502.FStar_TypeChecker_Cfg.reifying)
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
                      (fun uu____10545  ->
                         fun stack1  ->
                           match uu____10545 with
                           | (a,aq) ->
                               let uu____10557 =
                                 let uu____10558 =
                                   let uu____10565 =
                                     let uu____10566 =
                                       let uu____10597 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____10597, false)  in
                                     Clos uu____10566  in
                                   (uu____10565, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____10558  in
                               uu____10557 :: stack1) args)
                  in
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____10685  ->
                     let uu____10686 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____10686);
                norm cfg env stack1 head1)
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
                             ((let uu___306_10734 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___306_10734.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___306_10734.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____10735 ->
                      let uu____10750 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10750)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____10753 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____10753 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____10784 =
                          let uu____10785 =
                            let uu____10792 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___307_10798 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___307_10798.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___307_10798.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____10792)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____10785  in
                        mk uu____10784 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____10821 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____10821
               else
                 (let uu____10823 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____10823 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____10831 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____10857  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____10831 c1  in
                      let t2 =
                        let uu____10881 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____10881 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____10994)::uu____10995 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11008  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____11009)::uu____11010 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11021  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____11022,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____11023;
                                   FStar_Syntax_Syntax.vars = uu____11024;_},uu____11025,uu____11026))::uu____11027
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11034  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____11035)::uu____11036 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11047  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____11048 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11051  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____11055  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____11080 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____11080
                         | FStar_Util.Inr c ->
                             let uu____11094 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____11094
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____11117 =
                               let uu____11118 =
                                 let uu____11145 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____11145, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11118
                                in
                             mk uu____11117 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____11180 ->
                           let uu____11181 =
                             let uu____11182 =
                               let uu____11183 =
                                 let uu____11210 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____11210, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____11183
                                in
                             mk uu____11182 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____11181))))
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
                   let uu___308_11287 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___309_11290 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___309_11290.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___309_11290.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___309_11290.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___309_11290.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___309_11290.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___309_11290.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___309_11290.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___309_11290.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___309_11290.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___309_11290.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___309_11290.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___309_11290.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___309_11290.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___309_11290.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___309_11290.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___309_11290.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___309_11290.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___309_11290.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___309_11290.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___309_11290.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___309_11290.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___309_11290.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___309_11290.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___309_11290.FStar_TypeChecker_Cfg.nbe_step)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___308_11287.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___308_11287.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___308_11287.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___308_11287.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___308_11287.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___308_11287.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___308_11287.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___308_11287.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____11326 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____11326 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___310_11346 = cfg  in
                               let uu____11347 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___310_11346.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____11347;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___310_11346.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___310_11346.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___310_11346.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___310_11346.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___310_11346.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___310_11346.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___310_11346.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____11354 =
                                 let uu____11355 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____11355  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____11354
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___311_11358 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___311_11358.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___311_11358.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___311_11358.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___311_11358.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____11359 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____11359
           | FStar_Syntax_Syntax.Tm_let
               ((uu____11370,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____11371;
                               FStar_Syntax_Syntax.lbunivs = uu____11372;
                               FStar_Syntax_Syntax.lbtyp = uu____11373;
                               FStar_Syntax_Syntax.lbeff = uu____11374;
                               FStar_Syntax_Syntax.lbdef = uu____11375;
                               FStar_Syntax_Syntax.lbattrs = uu____11376;
                               FStar_Syntax_Syntax.lbpos = uu____11377;_}::uu____11378),uu____11379)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name
                   cfg.FStar_TypeChecker_Cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____11419 =
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
               if uu____11419
               then
                 let binder =
                   let uu____11421 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____11421  in
                 let env1 =
                   let uu____11431 =
                     let uu____11438 =
                       let uu____11439 =
                         let uu____11470 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____11470,
                           false)
                          in
                       Clos uu____11439  in
                     ((FStar_Pervasives_Native.Some binder), uu____11438)  in
                   uu____11431 :: env  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____11565  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                 then
                   (FStar_TypeChecker_Cfg.log cfg
                      (fun uu____11569  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____11570 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____11570))
                 else
                   (let uu____11572 =
                      let uu____11577 =
                        let uu____11578 =
                          let uu____11585 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____11585
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____11578]  in
                      FStar_Syntax_Subst.open_term uu____11577 body  in
                    match uu____11572 with
                    | (bs,body1) ->
                        (FStar_TypeChecker_Cfg.log cfg
                           (fun uu____11612  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____11620 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____11620  in
                            FStar_Util.Inl
                              (let uu___312_11636 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___312_11636.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___312_11636.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____11639  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___313_11641 = lb  in
                             let uu____11642 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___313_11641.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___313_11641.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____11642;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___313_11641.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___313_11641.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11671  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___314_11696 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps =
                                 (uu___314_11696.FStar_TypeChecker_Cfg.steps);
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___314_11696.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___314_11696.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 (uu___314_11696.FStar_TypeChecker_Cfg.delta_level);
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___314_11696.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong = true;
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___314_11696.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___314_11696.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___314_11696.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           FStar_TypeChecker_Cfg.log cfg1
                             (fun uu____11699  ->
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
               let uu____11716 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____11716 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____11752 =
                               let uu___315_11753 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___315_11753.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___315_11753.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____11752  in
                           let uu____11754 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____11754 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____11780 =
                                   FStar_List.map (fun uu____11796  -> dummy)
                                     lbs1
                                    in
                                 let uu____11797 =
                                   let uu____11806 =
                                     FStar_List.map
                                       (fun uu____11828  -> dummy) xs1
                                      in
                                   FStar_List.append uu____11806 env  in
                                 FStar_List.append uu____11780 uu____11797
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____11854 =
                                       let uu___316_11855 = rc  in
                                       let uu____11856 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___316_11855.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____11856;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___316_11855.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____11854
                                 | uu____11865 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___317_11871 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___317_11871.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___317_11871.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___317_11871.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___317_11871.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____11881 =
                        FStar_List.map (fun uu____11897  -> dummy) lbs2  in
                      FStar_List.append uu____11881 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____11905 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____11905 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___318_11921 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___318_11921.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___318_11921.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
               ->
               let uu____11950 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____11950
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____11969 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____12045  ->
                        match uu____12045 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___319_12166 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___319_12166.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___319_12166.FStar_Syntax_Syntax.sort)
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
               (match uu____11969 with
                | (rec_env,memos,uu____12393) ->
                    let uu____12446 =
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
                             let uu____12757 =
                               let uu____12764 =
                                 let uu____12765 =
                                   let uu____12796 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____12796, false)
                                    in
                                 Clos uu____12765  in
                               (FStar_Pervasives_Native.None, uu____12764)
                                in
                             uu____12757 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____12900  ->
                     let uu____12901 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____12901);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____12923 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____12925::uu____12926 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____12931) ->
                                 norm cfg env ((Meta (env, m, r)) :: stack)
                                   head1
                             | FStar_Syntax_Syntax.Meta_pattern args ->
                                 let args1 = norm_pattern_args cfg env args
                                    in
                                 norm cfg env
                                   ((Meta
                                       (env,
                                         (FStar_Syntax_Syntax.Meta_pattern
                                            args1),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____12958 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____12974 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____12974
                              | uu____12987 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____12993 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____13017 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____13031 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____13044 =
                        let uu____13045 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____13046 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____13045 uu____13046
                         in
                      failwith uu____13044
                    else
                      (let uu____13048 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____13048)
                | uu____13049 -> norm cfg env stack t2))

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
              let uu____13058 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____13058 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____13072  ->
                        let uu____13073 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____13073);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____13084  ->
                        let uu____13085 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____13086 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____13085 uu____13086);
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
                      | (UnivArgs (us',uu____13099))::stack1 ->
                          ((let uu____13108 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____13108
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____13112 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____13112) us'
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
                      | uu____13145 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____13148 ->
                          let uu____13151 =
                            let uu____13152 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____13152
                             in
                          failwith uu____13151
                    else norm cfg env stack t1))

and (reduce_impure_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      stack ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.monad_name,(FStar_Syntax_Syntax.monad_name,
                                            FStar_Syntax_Syntax.monad_name)
                                            FStar_Pervasives_Native.tuple2)
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
                  let uu___320_13176 = cfg  in
                  let uu____13177 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____13177;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___320_13176.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___320_13176.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___320_13176.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___320_13176.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___320_13176.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___320_13176.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___320_13176.FStar_TypeChecker_Cfg.reifying)
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
                     (uu____13207,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____13208;
                                    FStar_Syntax_Syntax.vars = uu____13209;_},uu____13210,uu____13211))::uu____13212
                     -> ()
                 | uu____13217 ->
                     let uu____13220 =
                       let uu____13221 = stack_to_string stack  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____13221
                        in
                     failwith uu____13220);
                (let head0 = head1  in
                 let head2 = FStar_Syntax_Util.unascribe head1  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____13228  ->
                      let uu____13229 = FStar_Syntax_Print.tag_of_term head2
                         in
                      let uu____13230 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____13229
                        uu____13230);
                 (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                  let uu____13232 =
                    let uu____13233 = FStar_Syntax_Subst.compress head3  in
                    uu____13233.FStar_Syntax_Syntax.n  in
                  match uu____13232 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let ed =
                        let uu____13251 =
                          FStar_TypeChecker_Env.norm_eff_name
                            cfg.FStar_TypeChecker_Cfg.tcenv m
                           in
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv uu____13251
                         in
                      let uu____13252 = ed.FStar_Syntax_Syntax.bind_repr  in
                      (match uu____13252 with
                       | (uu____13253,bind_repr) ->
                           (match lb.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____13263 ->
                                failwith
                                  "Cannot reify a top-level let binding"
                            | FStar_Util.Inl x ->
                                let is_return e =
                                  let uu____13273 =
                                    let uu____13274 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____13274.FStar_Syntax_Syntax.n  in
                                  match uu____13273 with
                                  | FStar_Syntax_Syntax.Tm_meta
                                      (e1,FStar_Syntax_Syntax.Meta_monadic
                                       (uu____13280,uu____13281))
                                      ->
                                      let uu____13290 =
                                        let uu____13291 =
                                          FStar_Syntax_Subst.compress e1  in
                                        uu____13291.FStar_Syntax_Syntax.n  in
                                      (match uu____13290 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                            (uu____13297,msrc,uu____13299))
                                           when
                                           FStar_Syntax_Util.is_pure_effect
                                             msrc
                                           ->
                                           let uu____13308 =
                                             FStar_Syntax_Subst.compress e2
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____13308
                                       | uu____13309 ->
                                           FStar_Pervasives_Native.None)
                                  | uu____13310 ->
                                      FStar_Pervasives_Native.None
                                   in
                                let uu____13311 =
                                  is_return lb.FStar_Syntax_Syntax.lbdef  in
                                (match uu____13311 with
                                 | FStar_Pervasives_Native.Some e ->
                                     let lb1 =
                                       let uu___321_13316 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___321_13316.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___321_13316.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           (uu___321_13316.FStar_Syntax_Syntax.lbtyp);
                                         FStar_Syntax_Syntax.lbeff =
                                           FStar_Parser_Const.effect_PURE_lid;
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___321_13316.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___321_13316.FStar_Syntax_Syntax.lbpos)
                                       }  in
                                     let uu____13317 = FStar_List.tl stack
                                        in
                                     let uu____13318 =
                                       let uu____13319 =
                                         let uu____13326 =
                                           let uu____13327 =
                                             let uu____13340 =
                                               FStar_Syntax_Util.mk_reify
                                                 body
                                                in
                                             ((false, [lb1]), uu____13340)
                                              in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____13327
                                            in
                                         FStar_Syntax_Syntax.mk uu____13326
                                          in
                                       uu____13319
                                         FStar_Pervasives_Native.None
                                         head3.FStar_Syntax_Syntax.pos
                                        in
                                     norm cfg env uu____13317 uu____13318
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____13356 =
                                       let uu____13357 = is_return body  in
                                       match uu____13357 with
                                       | FStar_Pervasives_Native.Some
                                           {
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_bvar y;
                                             FStar_Syntax_Syntax.pos =
                                               uu____13361;
                                             FStar_Syntax_Syntax.vars =
                                               uu____13362;_}
                                           -> FStar_Syntax_Syntax.bv_eq x y
                                       | uu____13365 -> false  in
                                     if uu____13356
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
                                          let uu____13386 =
                                            let uu____13393 =
                                              let uu____13394 =
                                                let uu____13413 =
                                                  let uu____13422 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____13422]  in
                                                (uu____13413, body1,
                                                  (FStar_Pervasives_Native.Some
                                                     body_rc))
                                                 in
                                              FStar_Syntax_Syntax.Tm_abs
                                                uu____13394
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____13393
                                             in
                                          uu____13386
                                            FStar_Pervasives_Native.None
                                            body1.FStar_Syntax_Syntax.pos
                                           in
                                        let close1 = closure_as_term cfg env
                                           in
                                        let bind_inst =
                                          let uu____13464 =
                                            let uu____13465 =
                                              FStar_Syntax_Subst.compress
                                                bind_repr
                                               in
                                            uu____13465.FStar_Syntax_Syntax.n
                                             in
                                          match uu____13464 with
                                          | FStar_Syntax_Syntax.Tm_uinst
                                              (bind1,uu____13471::uu____13472::[])
                                              ->
                                              let uu____13477 =
                                                let uu____13484 =
                                                  let uu____13485 =
                                                    let uu____13492 =
                                                      let uu____13493 =
                                                        let uu____13494 =
                                                          close1
                                                            lb.FStar_Syntax_Syntax.lbtyp
                                                           in
                                                        (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.FStar_TypeChecker_Cfg.tcenv
                                                          uu____13494
                                                         in
                                                      let uu____13495 =
                                                        let uu____13498 =
                                                          let uu____13499 =
                                                            close1 t  in
                                                          (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                            cfg.FStar_TypeChecker_Cfg.tcenv
                                                            uu____13499
                                                           in
                                                        [uu____13498]  in
                                                      uu____13493 ::
                                                        uu____13495
                                                       in
                                                    (bind1, uu____13492)  in
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                    uu____13485
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____13484
                                                 in
                                              uu____13477
                                                FStar_Pervasives_Native.None
                                                rng
                                          | uu____13505 ->
                                              failwith
                                                "NIY : Reification of indexed effects"
                                           in
                                        let maybe_range_arg =
                                          let uu____13519 =
                                            FStar_Util.for_some
                                              (FStar_Syntax_Util.attr_eq
                                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                                              ed.FStar_Syntax_Syntax.eff_attrs
                                             in
                                          if uu____13519
                                          then
                                            let uu____13530 =
                                              let uu____13539 =
                                                FStar_TypeChecker_Cfg.embed_simple
                                                  FStar_Syntax_Embeddings.e_range
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____13539
                                               in
                                            let uu____13540 =
                                              let uu____13551 =
                                                let uu____13560 =
                                                  FStar_TypeChecker_Cfg.embed_simple
                                                    FStar_Syntax_Embeddings.e_range
                                                    body2.FStar_Syntax_Syntax.pos
                                                    body2.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Syntax_Syntax.as_arg
                                                  uu____13560
                                                 in
                                              [uu____13551]  in
                                            uu____13530 :: uu____13540
                                          else []  in
                                        let reified =
                                          let uu____13597 =
                                            let uu____13604 =
                                              let uu____13605 =
                                                let uu____13622 =
                                                  let uu____13633 =
                                                    let uu____13644 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        lb.FStar_Syntax_Syntax.lbtyp
                                                       in
                                                    let uu____13653 =
                                                      let uu____13664 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          t
                                                         in
                                                      [uu____13664]  in
                                                    uu____13644 ::
                                                      uu____13653
                                                     in
                                                  let uu____13697 =
                                                    let uu____13708 =
                                                      let uu____13719 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          FStar_Syntax_Syntax.tun
                                                         in
                                                      let uu____13728 =
                                                        let uu____13739 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            head4
                                                           in
                                                        let uu____13748 =
                                                          let uu____13759 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          let uu____13768 =
                                                            let uu____13779 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                body2
                                                               in
                                                            [uu____13779]  in
                                                          uu____13759 ::
                                                            uu____13768
                                                           in
                                                        uu____13739 ::
                                                          uu____13748
                                                         in
                                                      uu____13719 ::
                                                        uu____13728
                                                       in
                                                    FStar_List.append
                                                      maybe_range_arg
                                                      uu____13708
                                                     in
                                                  FStar_List.append
                                                    uu____13633 uu____13697
                                                   in
                                                (bind_inst, uu____13622)  in
                                              FStar_Syntax_Syntax.Tm_app
                                                uu____13605
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____13604
                                             in
                                          uu____13597
                                            FStar_Pervasives_Native.None rng
                                           in
                                        FStar_TypeChecker_Cfg.log cfg
                                          (fun uu____13863  ->
                                             let uu____13864 =
                                               FStar_Syntax_Print.term_to_string
                                                 head0
                                                in
                                             let uu____13865 =
                                               FStar_Syntax_Print.term_to_string
                                                 reified
                                                in
                                             FStar_Util.print2
                                               "Reified (1) <%s> to %s\n"
                                               uu____13864 uu____13865);
                                        (let uu____13866 =
                                           FStar_List.tl stack  in
                                         norm cfg env uu____13866 reified)))))
                  | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                      ((let uu____13894 = FStar_Options.defensive ()  in
                        if uu____13894
                        then
                          let is_arg_impure uu____13906 =
                            match uu____13906 with
                            | (e,q) ->
                                let uu____13919 =
                                  let uu____13920 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____13920.FStar_Syntax_Syntax.n  in
                                (match uu____13919 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____13935 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____13935
                                 | uu____13936 -> false)
                             in
                          let uu____13937 =
                            let uu____13938 =
                              let uu____13949 =
                                FStar_Syntax_Syntax.as_arg head_app  in
                              uu____13949 :: args  in
                            FStar_Util.for_some is_arg_impure uu____13938  in
                          (if uu____13937
                           then
                             let uu____13974 =
                               let uu____13979 =
                                 let uu____13980 =
                                   FStar_Syntax_Print.term_to_string head3
                                    in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____13980
                                  in
                               (FStar_Errors.Warning_Defensive, uu____13979)
                                in
                             FStar_Errors.log_issue
                               head3.FStar_Syntax_Syntax.pos uu____13974
                           else ())
                        else ());
                       (let fallback1 uu____13988 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____13992  ->
                               let uu____13993 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____13993 "");
                          (let uu____13994 = FStar_List.tl stack  in
                           let uu____13995 = FStar_Syntax_Util.mk_reify head3
                              in
                           norm cfg env uu____13994 uu____13995)
                           in
                        let fallback2 uu____14001 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____14005  ->
                               let uu____14006 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____14006 "");
                          (let uu____14007 = FStar_List.tl stack  in
                           let uu____14008 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (head3,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               head0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env uu____14007 uu____14008)
                           in
                        let uu____14013 =
                          let uu____14014 =
                            FStar_Syntax_Util.un_uinst head_app  in
                          uu____14014.FStar_Syntax_Syntax.n  in
                        match uu____14013 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____14020 =
                              let uu____14021 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____14021  in
                            if uu____14020
                            then fallback1 ()
                            else
                              (let uu____14023 =
                                 let uu____14024 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____14024  in
                               if uu____14023
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____14039 =
                                      let uu____14044 =
                                        FStar_Syntax_Util.mk_reify head_app
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____14044 args
                                       in
                                    uu____14039 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____14047 = FStar_List.tl stack  in
                                  norm cfg env uu____14047 t1))
                        | uu____14048 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____14050) ->
                      do_reify_monadic fallback cfg env stack e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____14074 = closure_as_term cfg env t'  in
                        reify_lift cfg e msrc mtgt uu____14074  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____14078  ->
                            let uu____14079 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____14079);
                       (let uu____14080 = FStar_List.tl stack  in
                        norm cfg env uu____14080 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                      let branches1 =
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun uu____14201  ->
                                match uu____14201 with
                                | (pat,wopt,tm) ->
                                    let uu____14249 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____14249)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                          head3.FStar_Syntax_Syntax.pos
                         in
                      let uu____14281 = FStar_List.tl stack  in
                      norm cfg env uu____14281 tm
                  | uu____14282 -> fallback ()))

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
              (fun uu____14296  ->
                 let uu____14297 = FStar_Ident.string_of_lid msrc  in
                 let uu____14298 = FStar_Ident.string_of_lid mtgt  in
                 let uu____14299 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____14297
                   uu____14298 uu____14299);
            (let uu____14300 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____14300
             then
               let ed =
                 let uu____14302 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____14302  in
               let uu____14303 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____14303 with
               | (uu____14304,return_repr) ->
                   let return_inst =
                     let uu____14317 =
                       let uu____14318 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____14318.FStar_Syntax_Syntax.n  in
                     match uu____14317 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____14324::[]) ->
                         let uu____14329 =
                           let uu____14336 =
                             let uu____14337 =
                               let uu____14344 =
                                 let uu____14345 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____14345]  in
                               (return_tm, uu____14344)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____14337  in
                           FStar_Syntax_Syntax.mk uu____14336  in
                         uu____14329 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____14351 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____14354 =
                     let uu____14361 =
                       let uu____14362 =
                         let uu____14379 =
                           let uu____14390 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____14399 =
                             let uu____14410 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____14410]  in
                           uu____14390 :: uu____14399  in
                         (return_inst, uu____14379)  in
                       FStar_Syntax_Syntax.Tm_app uu____14362  in
                     FStar_Syntax_Syntax.mk uu____14361  in
                   uu____14354 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____14459 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____14459 with
                | FStar_Pervasives_Native.None  ->
                    let uu____14462 =
                      let uu____14463 = FStar_Ident.text_of_lid msrc  in
                      let uu____14464 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____14463 uu____14464
                       in
                    failwith uu____14462
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14465;
                      FStar_TypeChecker_Env.mtarget = uu____14466;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14467;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____14489 =
                      let uu____14490 = FStar_Ident.text_of_lid msrc  in
                      let uu____14491 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____14490 uu____14491
                       in
                    failwith uu____14489
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14492;
                      FStar_TypeChecker_Env.mtarget = uu____14493;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14494;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____14529 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____14530 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____14529 t FStar_Syntax_Syntax.tun uu____14530))

and (norm_pattern_args :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                              FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                                FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2 Prims.list Prims.list)
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____14600  ->
                   match uu____14600 with
                   | (a,imp) ->
                       let uu____14619 = norm cfg env [] a  in
                       (uu____14619, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____14629  ->
             let uu____14630 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____14631 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____14630 uu____14631);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____14655 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____14655
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___322_14658 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___322_14658.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___322_14658.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____14680 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____14680
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___323_14683 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___323_14683.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___323_14683.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____14728  ->
                      match uu____14728 with
                      | (a,i) ->
                          let uu____14747 = norm cfg env [] a  in
                          (uu____14747, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___267_14769  ->
                       match uu___267_14769 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____14773 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____14773
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___324_14781 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___325_14784 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___325_14784.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___324_14781.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___324_14781.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun b  ->
        let uu____14788 = b  in
        match uu____14788 with
        | (x,imp) ->
            let x1 =
              let uu___326_14796 = x  in
              let uu____14797 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___326_14796.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___326_14796.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____14797
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____14808 =
                    let uu____14809 = closure_as_term cfg env t  in
                    FStar_Syntax_Syntax.Meta uu____14809  in
                  FStar_Pervasives_Native.Some uu____14808
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____14820 =
          FStar_List.fold_left
            (fun uu____14854  ->
               fun b  ->
                 match uu____14854 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____14820 with | (nbs,uu____14934) -> FStar_List.rev nbs

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
            let flags1 =
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags
               in
            let uu____14966 =
              let uu___327_14967 = rc  in
              let uu____14968 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___327_14967.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____14968;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___327_14967.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____14966
        | uu____14977 -> lopt

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
            (let uu____14986 = FStar_Syntax_Print.term_to_string tm  in
             let uu____14987 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____14986 uu____14987)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___268_14991  ->
      match uu___268_14991 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____15004 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____15004 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____15008 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____15008)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____15016 = norm_cb cfg  in
            reduce_primops uu____15016 cfg env tm  in
          let uu____15023 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____15023
          then tm1
          else
            (let w t =
               let uu___328_15037 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___328_15037.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___328_15037.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____15048 =
                 let uu____15049 = FStar_Syntax_Util.unmeta t  in
                 uu____15049.FStar_Syntax_Syntax.n  in
               match uu____15048 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____15056 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____15117)::args1,(bv,uu____15120)::bs1) ->
                   let uu____15174 =
                     let uu____15175 = FStar_Syntax_Subst.compress t  in
                     uu____15175.FStar_Syntax_Syntax.n  in
                   (match uu____15174 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____15179 -> false)
               | ([],[]) -> true
               | (uu____15208,uu____15209) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____15258 = FStar_Syntax_Print.term_to_string t  in
                  let uu____15259 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____15258
                    uu____15259)
               else ();
               (let uu____15261 = FStar_Syntax_Util.head_and_args' t  in
                match uu____15261 with
                | (hd1,args) ->
                    let uu____15300 =
                      let uu____15301 = FStar_Syntax_Subst.compress hd1  in
                      uu____15301.FStar_Syntax_Syntax.n  in
                    (match uu____15300 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____15308 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____15309 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____15310 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____15308 uu____15309 uu____15310)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____15312 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____15329 = FStar_Syntax_Print.term_to_string t  in
                  let uu____15330 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____15329
                    uu____15330)
               else ();
               (let uu____15332 = FStar_Syntax_Util.is_squash t  in
                match uu____15332 with
                | FStar_Pervasives_Native.Some (uu____15343,t') ->
                    is_applied bs t'
                | uu____15355 ->
                    let uu____15364 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____15364 with
                     | FStar_Pervasives_Native.Some (uu____15375,t') ->
                         is_applied bs t'
                     | uu____15387 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____15411 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____15411 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____15418)::(q,uu____15420)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____15462 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____15463 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____15462 uu____15463)
                    else ();
                    (let uu____15465 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____15465 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____15470 =
                           let uu____15471 = FStar_Syntax_Subst.compress p
                              in
                           uu____15471.FStar_Syntax_Syntax.n  in
                         (match uu____15470 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____15479 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____15479))
                          | uu____15482 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____15485)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____15510 =
                           let uu____15511 = FStar_Syntax_Subst.compress p1
                              in
                           uu____15511.FStar_Syntax_Syntax.n  in
                         (match uu____15510 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____15519 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____15519))
                          | uu____15522 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____15526 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____15526 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____15531 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____15531 with
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
                                     let uu____15542 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____15542))
                               | uu____15545 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____15550)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____15575 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____15575 with
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
                                     let uu____15586 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____15586))
                               | uu____15589 -> FStar_Pervasives_Native.None)
                          | uu____15592 -> FStar_Pervasives_Native.None)
                     | uu____15595 -> FStar_Pervasives_Native.None))
               | uu____15598 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____15611 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____15611 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____15617)::[],uu____15618,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____15637 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____15638 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____15637
                         uu____15638)
                    else ();
                    is_quantified_const bv phi')
               | uu____15640 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____15653 =
                 let uu____15654 = FStar_Syntax_Subst.compress phi  in
                 uu____15654.FStar_Syntax_Syntax.n  in
               match uu____15653 with
               | FStar_Syntax_Syntax.Tm_match (uu____15659,br::brs) ->
                   let uu____15726 = br  in
                   (match uu____15726 with
                    | (uu____15743,uu____15744,e) ->
                        let r =
                          let uu____15765 = simp_t e  in
                          match uu____15765 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____15771 =
                                FStar_List.for_all
                                  (fun uu____15789  ->
                                     match uu____15789 with
                                     | (uu____15802,uu____15803,e') ->
                                         let uu____15817 = simp_t e'  in
                                         uu____15817 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____15771
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____15825 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____15834 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____15834
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____15869 =
                 match uu____15869 with
                 | (t1,q) ->
                     let uu____15890 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____15890 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____15922 -> (t1, q))
                  in
               let uu____15935 = FStar_Syntax_Util.head_and_args t  in
               match uu____15935 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____16013 =
                 let uu____16014 = FStar_Syntax_Util.unmeta ty  in
                 uu____16014.FStar_Syntax_Syntax.n  in
               match uu____16013 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____16018) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____16023,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____16047 -> false  in
             let simplify1 arg =
               let uu____16078 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____16078, arg)  in
             let uu____16091 = is_forall_const tm1  in
             match uu____16091 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____16096 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____16097 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____16096
                       uu____16097)
                  else ();
                  (let uu____16099 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____16099))
             | FStar_Pervasives_Native.None  ->
                 let uu____16100 =
                   let uu____16101 = FStar_Syntax_Subst.compress tm1  in
                   uu____16101.FStar_Syntax_Syntax.n  in
                 (match uu____16100 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____16105;
                              FStar_Syntax_Syntax.vars = uu____16106;_},uu____16107);
                         FStar_Syntax_Syntax.pos = uu____16108;
                         FStar_Syntax_Syntax.vars = uu____16109;_},args)
                      ->
                      let uu____16139 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____16139
                      then
                        let uu____16140 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____16140 with
                         | (FStar_Pervasives_Native.Some (true ),uu____16195)::
                             (uu____16196,(arg,uu____16198))::[] ->
                             maybe_auto_squash arg
                         | (uu____16263,(arg,uu____16265))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____16266)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____16331)::uu____16332::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____16395::(FStar_Pervasives_Native.Some (false
                                         ),uu____16396)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____16459 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____16475 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____16475
                         then
                           let uu____16476 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____16476 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____16531)::uu____16532::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____16595::(FStar_Pervasives_Native.Some (true
                                           ),uu____16596)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____16659)::(uu____16660,(arg,uu____16662))::[]
                               -> maybe_auto_squash arg
                           | (uu____16727,(arg,uu____16729))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____16730)::[]
                               -> maybe_auto_squash arg
                           | uu____16795 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____16811 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____16811
                            then
                              let uu____16812 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____16812 with
                              | uu____16867::(FStar_Pervasives_Native.Some
                                              (true ),uu____16868)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____16931)::uu____16932::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____16995)::(uu____16996,(arg,uu____16998))::[]
                                  -> maybe_auto_squash arg
                              | (uu____17063,(p,uu____17065))::(uu____17066,
                                                                (q,uu____17068))::[]
                                  ->
                                  let uu____17133 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____17133
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____17135 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____17151 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____17151
                               then
                                 let uu____17152 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____17152 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17207)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17208)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17273)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____17274)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17339)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____17340)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17405)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17406)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____17471,(arg,uu____17473))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____17474)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17539)::(uu____17540,(arg,uu____17542))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____17607,(arg,uu____17609))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____17610)::[]
                                     ->
                                     let uu____17675 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17675
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17676)::(uu____17677,(arg,uu____17679))::[]
                                     ->
                                     let uu____17744 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17744
                                 | (uu____17745,(p,uu____17747))::(uu____17748,
                                                                   (q,uu____17750))::[]
                                     ->
                                     let uu____17815 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____17815
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____17817 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____17833 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____17833
                                  then
                                    let uu____17834 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____17834 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____17889)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____17928)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____17967 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____17983 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____17983
                                     then
                                       match args with
                                       | (t,uu____17985)::[] ->
                                           let uu____18010 =
                                             let uu____18011 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____18011.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____18010 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____18014::[],body,uu____18016)
                                                ->
                                                let uu____18051 = simp_t body
                                                   in
                                                (match uu____18051 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____18054 -> tm1)
                                            | uu____18057 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____18059))::(t,uu____18061)::[]
                                           ->
                                           let uu____18100 =
                                             let uu____18101 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____18101.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____18100 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____18104::[],body,uu____18106)
                                                ->
                                                let uu____18141 = simp_t body
                                                   in
                                                (match uu____18141 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____18144 -> tm1)
                                            | uu____18147 -> tm1)
                                       | uu____18148 -> tm1
                                     else
                                       (let uu____18160 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____18160
                                        then
                                          match args with
                                          | (t,uu____18162)::[] ->
                                              let uu____18187 =
                                                let uu____18188 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____18188.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____18187 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____18191::[],body,uu____18193)
                                                   ->
                                                   let uu____18228 =
                                                     simp_t body  in
                                                   (match uu____18228 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____18231 -> tm1)
                                               | uu____18234 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____18236))::(t,uu____18238)::[]
                                              ->
                                              let uu____18277 =
                                                let uu____18278 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____18278.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____18277 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____18281::[],body,uu____18283)
                                                   ->
                                                   let uu____18318 =
                                                     simp_t body  in
                                                   (match uu____18318 with
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
                                                    | uu____18321 -> tm1)
                                               | uu____18324 -> tm1)
                                          | uu____18325 -> tm1
                                        else
                                          (let uu____18337 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____18337
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18338;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18339;_},uu____18340)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18365;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18366;_},uu____18367)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____18392 -> tm1
                                           else
                                             (let uu____18404 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____18404 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____18424 ->
                                                  let uu____18433 =
                                                    let uu____18440 =
                                                      norm_cb cfg  in
                                                    reduce_equality
                                                      uu____18440 cfg env
                                                     in
                                                  uu____18433 tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____18448;
                         FStar_Syntax_Syntax.vars = uu____18449;_},args)
                      ->
                      let uu____18475 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18475
                      then
                        let uu____18476 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18476 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18531)::
                             (uu____18532,(arg,uu____18534))::[] ->
                             maybe_auto_squash arg
                         | (uu____18599,(arg,uu____18601))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18602)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18667)::uu____18668::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18731::(FStar_Pervasives_Native.Some (false
                                         ),uu____18732)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18795 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18811 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18811
                         then
                           let uu____18812 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18812 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18867)::uu____18868::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18931::(FStar_Pervasives_Native.Some (true
                                           ),uu____18932)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18995)::(uu____18996,(arg,uu____18998))::[]
                               -> maybe_auto_squash arg
                           | (uu____19063,(arg,uu____19065))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19066)::[]
                               -> maybe_auto_squash arg
                           | uu____19131 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19147 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19147
                            then
                              let uu____19148 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19148 with
                              | uu____19203::(FStar_Pervasives_Native.Some
                                              (true ),uu____19204)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19267)::uu____19268::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19331)::(uu____19332,(arg,uu____19334))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19399,(p,uu____19401))::(uu____19402,
                                                                (q,uu____19404))::[]
                                  ->
                                  let uu____19469 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19469
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19471 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19487 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19487
                               then
                                 let uu____19488 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19488 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19543)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19544)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19609)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19610)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19675)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19676)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19741)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19742)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19807,(arg,uu____19809))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19810)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19875)::(uu____19876,(arg,uu____19878))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19943,(arg,uu____19945))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19946)::[]
                                     ->
                                     let uu____20011 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20011
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20012)::(uu____20013,(arg,uu____20015))::[]
                                     ->
                                     let uu____20080 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20080
                                 | (uu____20081,(p,uu____20083))::(uu____20084,
                                                                   (q,uu____20086))::[]
                                     ->
                                     let uu____20151 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____20151
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____20153 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____20169 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____20169
                                  then
                                    let uu____20170 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____20170 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20225)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____20264)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20303 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20319 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____20319
                                     then
                                       match args with
                                       | (t,uu____20321)::[] ->
                                           let uu____20346 =
                                             let uu____20347 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20347.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20346 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20350::[],body,uu____20352)
                                                ->
                                                let uu____20387 = simp_t body
                                                   in
                                                (match uu____20387 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20390 -> tm1)
                                            | uu____20393 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20395))::(t,uu____20397)::[]
                                           ->
                                           let uu____20436 =
                                             let uu____20437 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20437.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20436 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20440::[],body,uu____20442)
                                                ->
                                                let uu____20477 = simp_t body
                                                   in
                                                (match uu____20477 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20480 -> tm1)
                                            | uu____20483 -> tm1)
                                       | uu____20484 -> tm1
                                     else
                                       (let uu____20496 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20496
                                        then
                                          match args with
                                          | (t,uu____20498)::[] ->
                                              let uu____20523 =
                                                let uu____20524 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20524.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20523 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20527::[],body,uu____20529)
                                                   ->
                                                   let uu____20564 =
                                                     simp_t body  in
                                                   (match uu____20564 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20567 -> tm1)
                                               | uu____20570 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20572))::(t,uu____20574)::[]
                                              ->
                                              let uu____20613 =
                                                let uu____20614 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20614.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20613 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20617::[],body,uu____20619)
                                                   ->
                                                   let uu____20654 =
                                                     simp_t body  in
                                                   (match uu____20654 with
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
                                                    | uu____20657 -> tm1)
                                               | uu____20660 -> tm1)
                                          | uu____20661 -> tm1
                                        else
                                          (let uu____20673 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20673
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20674;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20675;_},uu____20676)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20701;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20702;_},uu____20703)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20728 -> tm1
                                           else
                                             (let uu____20740 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20740 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20760 ->
                                                  let uu____20769 =
                                                    let uu____20776 =
                                                      norm_cb cfg  in
                                                    reduce_equality
                                                      uu____20776 cfg env
                                                     in
                                                  uu____20769 tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____20789 = simp_t t  in
                      (match uu____20789 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____20792 ->
                      let uu____20815 = is_const_match tm1  in
                      (match uu____20815 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____20818 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____20828  ->
               (let uu____20830 = FStar_Syntax_Print.tag_of_term t  in
                let uu____20831 = FStar_Syntax_Print.term_to_string t  in
                let uu____20832 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____20839 =
                  let uu____20840 =
                    let uu____20843 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____20843
                     in
                  stack_to_string uu____20840  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____20830 uu____20831 uu____20832 uu____20839);
               (let uu____20866 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____20866
                then
                  let uu____20867 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____20867 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____20874 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____20875 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____20876 =
                          let uu____20877 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____20877
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____20874
                          uu____20875 uu____20876);
                       failwith "DIE!")
                else ()));
          (let t1 = maybe_simplify cfg env stack t  in
           match stack with
           | [] -> t1
           | (Debug (tm,time_then))::stack1 ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then
                  (let time_now = FStar_Util.now ()  in
                   let uu____20895 =
                     let uu____20896 =
                       let uu____20897 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____20897  in
                     FStar_Util.string_of_int uu____20896  in
                   let uu____20902 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____20903 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____20895 uu____20902 uu____20903)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____20909,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                FStar_TypeChecker_Cfg.log cfg
                  (fun uu____20960  ->
                     let uu____20961 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____20961);
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
               let uu____20999 =
                 let uu___329_21000 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___329_21000.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___329_21000.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____20999
           | (Arg (Univ uu____21003,uu____21004,uu____21005))::uu____21006 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____21009,uu____21010))::uu____21011 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____21026,uu____21027),aq,r))::stack1
               when
               let uu____21077 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____21077 ->
               let t2 =
                 let uu____21081 =
                   let uu____21086 =
                     let uu____21087 = closure_as_term cfg env_arg tm  in
                     (uu____21087, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____21086  in
                 uu____21081 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____21099),aq,r))::stack1 ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____21152  ->
                     let uu____21153 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____21153);
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
                  (let uu____21167 = FStar_ST.op_Bang m  in
                   match uu____21167 with
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
                         (let stack2 = (MemoLazy m) :: (App (env, t1, aq, r))
                            :: stack1  in
                          norm cfg env_arg stack2 tm)
                   | FStar_Pervasives_Native.Some (uu____21308,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____21363 =
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____21367  ->
                      let uu____21368 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____21368);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____21376 =
                 let uu____21377 = FStar_Syntax_Subst.compress t1  in
                 uu____21377.FStar_Syntax_Syntax.n  in
               (match uu____21376 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____21404 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____21404  in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____21408  ->
                          let uu____21409 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____21409);
                     (let uu____21410 = FStar_List.tl stack  in
                      norm cfg env1 uu____21410 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____21411);
                       FStar_Syntax_Syntax.pos = uu____21412;
                       FStar_Syntax_Syntax.vars = uu____21413;_},(e,uu____21415)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____21454 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                    ->
                    let uu____21471 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____21471 with
                     | (hd1,args) ->
                         let uu____21514 =
                           let uu____21515 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____21515.FStar_Syntax_Syntax.n  in
                         (match uu____21514 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____21519 =
                                FStar_TypeChecker_Cfg.find_prim_step cfg fv
                                 in
                              (match uu____21519 with
                               | FStar_Pervasives_Native.Some
                                   {
                                     FStar_TypeChecker_Cfg.name = uu____21522;
                                     FStar_TypeChecker_Cfg.arity =
                                       uu____21523;
                                     FStar_TypeChecker_Cfg.univ_arity =
                                       uu____21524;
                                     FStar_TypeChecker_Cfg.auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     FStar_TypeChecker_Cfg.strong_reduction_ok
                                       = uu____21526;
                                     FStar_TypeChecker_Cfg.requires_binder_substitution
                                       = uu____21527;
                                     FStar_TypeChecker_Cfg.interpretation =
                                       uu____21528;
                                     FStar_TypeChecker_Cfg.interpretation_nbe
                                       = uu____21529;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____21559 -> fallback " (3)" ())
                          | uu____21562 -> fallback " (4)" ()))
                | uu____21563 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (FStar_TypeChecker_Cfg.log cfg1
                  (fun uu____21588  ->
                     let uu____21589 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____21589);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____21598 =
                   FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____21603  ->
                        let uu____21604 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____21605 =
                          let uu____21606 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____21633  ->
                                    match uu____21633 with
                                    | (p,uu____21643,uu____21644) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____21606
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____21604 uu____21605);
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
                             (fun uu___269_21661  ->
                                match uu___269_21661 with
                                | FStar_TypeChecker_Env.InliningDelta  ->
                                    true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____21662 -> false))
                         in
                      let steps =
                        let uu___330_21664 = cfg1.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___330_21664.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___330_21664.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta = false;
                          FStar_TypeChecker_Cfg.weak =
                            (uu___330_21664.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___330_21664.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___330_21664.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___330_21664.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___330_21664.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_tac = false;
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___330_21664.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___330_21664.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___330_21664.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___330_21664.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___330_21664.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___330_21664.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___330_21664.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___330_21664.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___330_21664.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___330_21664.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___330_21664.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___330_21664.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___330_21664.FStar_TypeChecker_Cfg.nbe_step)
                        }  in
                      let uu___331_21669 = cfg1  in
                      {
                        FStar_TypeChecker_Cfg.steps = steps;
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___331_21669.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___331_21669.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level = new_delta;
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___331_21669.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong = true;
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___331_21669.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___331_21669.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying =
                          (uu___331_21669.FStar_TypeChecker_Cfg.reifying)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____21741 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____21770 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____21854  ->
                                    fun uu____21855  ->
                                      match (uu____21854, uu____21855) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____21994 = norm_pat env3 p1
                                             in
                                          (match uu____21994 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____21770 with
                           | (pats1,env3) ->
                               ((let uu___332_22156 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___332_22156.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___333_22175 = x  in
                            let uu____22176 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___333_22175.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___333_22175.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____22176
                            }  in
                          ((let uu___334_22190 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___334_22190.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___335_22201 = x  in
                            let uu____22202 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___335_22201.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___335_22201.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____22202
                            }  in
                          ((let uu___336_22216 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___336_22216.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___337_22232 = x  in
                            let uu____22233 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___337_22232.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___337_22232.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____22233
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___338_22248 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___338_22248.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____22292 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____22322 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____22322 with
                                  | (p,wopt,e) ->
                                      let uu____22342 = norm_pat env1 p  in
                                      (match uu____22342 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____22397 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____22397
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____22414 =
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
                      if uu____22414
                      then
                        norm
                          (let uu___339_22419 = cfg1  in
                           {
                             FStar_TypeChecker_Cfg.steps =
                               (let uu___340_22422 =
                                  cfg1.FStar_TypeChecker_Cfg.steps  in
                                {
                                  FStar_TypeChecker_Cfg.beta =
                                    (uu___340_22422.FStar_TypeChecker_Cfg.beta);
                                  FStar_TypeChecker_Cfg.iota =
                                    (uu___340_22422.FStar_TypeChecker_Cfg.iota);
                                  FStar_TypeChecker_Cfg.zeta =
                                    (uu___340_22422.FStar_TypeChecker_Cfg.zeta);
                                  FStar_TypeChecker_Cfg.weak =
                                    (uu___340_22422.FStar_TypeChecker_Cfg.weak);
                                  FStar_TypeChecker_Cfg.hnf =
                                    (uu___340_22422.FStar_TypeChecker_Cfg.hnf);
                                  FStar_TypeChecker_Cfg.primops =
                                    (uu___340_22422.FStar_TypeChecker_Cfg.primops);
                                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                    =
                                    (uu___340_22422.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                  FStar_TypeChecker_Cfg.unfold_until =
                                    (uu___340_22422.FStar_TypeChecker_Cfg.unfold_until);
                                  FStar_TypeChecker_Cfg.unfold_only =
                                    (uu___340_22422.FStar_TypeChecker_Cfg.unfold_only);
                                  FStar_TypeChecker_Cfg.unfold_fully =
                                    (uu___340_22422.FStar_TypeChecker_Cfg.unfold_fully);
                                  FStar_TypeChecker_Cfg.unfold_attr =
                                    (uu___340_22422.FStar_TypeChecker_Cfg.unfold_attr);
                                  FStar_TypeChecker_Cfg.unfold_tac =
                                    (uu___340_22422.FStar_TypeChecker_Cfg.unfold_tac);
                                  FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                    =
                                    (uu___340_22422.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                  FStar_TypeChecker_Cfg.simplify =
                                    (uu___340_22422.FStar_TypeChecker_Cfg.simplify);
                                  FStar_TypeChecker_Cfg.erase_universes =
                                    (uu___340_22422.FStar_TypeChecker_Cfg.erase_universes);
                                  FStar_TypeChecker_Cfg.allow_unbound_universes
                                    =
                                    (uu___340_22422.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                  FStar_TypeChecker_Cfg.reify_ =
                                    (uu___340_22422.FStar_TypeChecker_Cfg.reify_);
                                  FStar_TypeChecker_Cfg.compress_uvars =
                                    (uu___340_22422.FStar_TypeChecker_Cfg.compress_uvars);
                                  FStar_TypeChecker_Cfg.no_full_norm =
                                    (uu___340_22422.FStar_TypeChecker_Cfg.no_full_norm);
                                  FStar_TypeChecker_Cfg.check_no_uvars =
                                    (uu___340_22422.FStar_TypeChecker_Cfg.check_no_uvars);
                                  FStar_TypeChecker_Cfg.unmeta =
                                    (uu___340_22422.FStar_TypeChecker_Cfg.unmeta);
                                  FStar_TypeChecker_Cfg.unascribe =
                                    (uu___340_22422.FStar_TypeChecker_Cfg.unascribe);
                                  FStar_TypeChecker_Cfg.in_full_norm_request
                                    =
                                    (uu___340_22422.FStar_TypeChecker_Cfg.in_full_norm_request);
                                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                    = false;
                                  FStar_TypeChecker_Cfg.nbe_step =
                                    (uu___340_22422.FStar_TypeChecker_Cfg.nbe_step)
                                });
                             FStar_TypeChecker_Cfg.tcenv =
                               (uu___339_22419.FStar_TypeChecker_Cfg.tcenv);
                             FStar_TypeChecker_Cfg.debug =
                               (uu___339_22419.FStar_TypeChecker_Cfg.debug);
                             FStar_TypeChecker_Cfg.delta_level =
                               (uu___339_22419.FStar_TypeChecker_Cfg.delta_level);
                             FStar_TypeChecker_Cfg.primitive_steps =
                               (uu___339_22419.FStar_TypeChecker_Cfg.primitive_steps);
                             FStar_TypeChecker_Cfg.strong =
                               (uu___339_22419.FStar_TypeChecker_Cfg.strong);
                             FStar_TypeChecker_Cfg.memoize_lazy =
                               (uu___339_22419.FStar_TypeChecker_Cfg.memoize_lazy);
                             FStar_TypeChecker_Cfg.normalize_pure_lets =
                               (uu___339_22419.FStar_TypeChecker_Cfg.normalize_pure_lets);
                             FStar_TypeChecker_Cfg.reifying =
                               (uu___339_22419.FStar_TypeChecker_Cfg.reifying)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____22424 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____22424)
                    in
                 let rec is_cons head1 =
                   let uu____22449 =
                     let uu____22450 = FStar_Syntax_Subst.compress head1  in
                     uu____22450.FStar_Syntax_Syntax.n  in
                   match uu____22449 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____22454) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____22459 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____22460;
                         FStar_Syntax_Syntax.fv_delta = uu____22461;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____22462;
                         FStar_Syntax_Syntax.fv_delta = uu____22463;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____22464);_}
                       -> true
                   | uu____22471 -> false  in
                 let guard_when_clause wopt b rest =
                   match wopt with
                   | FStar_Pervasives_Native.None  -> b
                   | FStar_Pervasives_Native.Some w ->
                       let then_branch = b  in
                       let else_branch =
                         mk (FStar_Syntax_Syntax.Tm_match (scrutinee, rest))
                           r
                          in
                       FStar_Syntax_Util.if_then_else w then_branch
                         else_branch
                    in
                 let rec matches_pat scrutinee_orig p =
                   let scrutinee1 = FStar_Syntax_Util.unmeta scrutinee_orig
                      in
                   let scrutinee2 = FStar_Syntax_Util.unlazy scrutinee1  in
                   let uu____22635 =
                     FStar_Syntax_Util.head_and_args scrutinee2  in
                   match uu____22635 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____22728 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee2.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____22767 ->
                                 let uu____22768 =
                                   let uu____22769 = is_cons head1  in
                                   Prims.op_Negation uu____22769  in
                                 FStar_Util.Inr uu____22768)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____22794 =
                              let uu____22795 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____22795.FStar_Syntax_Syntax.n  in
                            (match uu____22794 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____22813 ->
                                 let uu____22814 =
                                   let uu____22815 = is_cons head1  in
                                   Prims.op_Negation uu____22815  in
                                 FStar_Util.Inr uu____22814))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____22898)::rest_a,(p1,uu____22901)::rest_p) ->
                       let uu____22955 = matches_pat t2 p1  in
                       (match uu____22955 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____23004 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____23124 = matches_pat scrutinee1 p1  in
                       (match uu____23124 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (FStar_TypeChecker_Cfg.log cfg1
                               (fun uu____23164  ->
                                  let uu____23165 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____23166 =
                                    let uu____23167 =
                                      FStar_List.map
                                        (fun uu____23177  ->
                                           match uu____23177 with
                                           | (uu____23182,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____23167
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____23165 uu____23166);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____23214  ->
                                       match uu____23214 with
                                       | (bv,t2) ->
                                           let uu____23237 =
                                             let uu____23244 =
                                               let uu____23247 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____23247
                                                in
                                             let uu____23248 =
                                               let uu____23249 =
                                                 let uu____23280 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____23280, false)
                                                  in
                                               Clos uu____23249  in
                                             (uu____23244, uu____23248)  in
                                           uu____23237 :: env2) env1 s
                                 in
                              let uu____23393 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____23393)))
                    in
                 if
                   (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                 then matches scrutinee branches
                 else norm_and_rebuild_match ())))

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
            (fun uu____23423  ->
               let uu____23424 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____23424);
          (let uu____23425 = is_nbe_request s  in
           if uu____23425
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____23429  ->
                   let uu____23430 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____23430);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____23434  ->
                   let uu____23435 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____23435);
              (let r = nbe_eval c s t  in
               FStar_TypeChecker_Cfg.log_top c
                 (fun uu____23440  ->
                    let uu____23441 = FStar_Syntax_Print.term_to_string r  in
                    FStar_Util.print1 "}\nNormalization result = (%s)\n"
                      uu____23441);
               r))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____23446  ->
                   let uu____23447 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____23447);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____23451  ->
                   let uu____23452 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____23452);
              (let r = norm c [] [] t  in
               FStar_TypeChecker_Cfg.log_top c
                 (fun uu____23463  ->
                    let uu____23464 = FStar_Syntax_Print.term_to_string r  in
                    FStar_Util.print1 "}\nNormalization result = (%s)\n"
                      uu____23464);
               r)))
  
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
        let uu____23495 = FStar_TypeChecker_Cfg.config s e  in
        norm_comp uu____23495 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____23512 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____23512 [] u
  
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
          FStar_TypeChecker_Env.EraseUniverses] env
         in
      let non_info t =
        let uu____23536 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____23536  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____23543 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___341_23562 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___341_23562.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___341_23562.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name
              cfg.FStar_TypeChecker_Cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____23569 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____23569
          then
            let ct1 =
              let uu____23571 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____23571 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____23578 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____23578
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___342_23582 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___342_23582.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___342_23582.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___342_23582.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev
                      cfg.FStar_TypeChecker_Cfg.tcenv c
                     in
                  let uu___343_23584 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___343_23584.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___343_23584.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___343_23584.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___343_23584.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___344_23585 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___344_23585.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___344_23585.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____23587 -> c
  
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
          FStar_TypeChecker_Env.AllowUnboundUniverses] env
         in
      let non_info t =
        let uu____23605 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____23605  in
      let uu____23612 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____23612
      then
        let uu____23613 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____23613 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____23619  ->
                 let uu____23620 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____23620)
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
          (fun uu___346_23634  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___345_23637 ->
            ((let uu____23639 =
                let uu____23644 =
                  let uu____23645 = FStar_Util.message_of_exn uu___345_23637
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23645
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____23644)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____23639);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          (fun uu___348_23659  ->
             match () with
             | () ->
                 let uu____23660 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____23660 [] c) ()
        with
        | uu___347_23669 ->
            ((let uu____23671 =
                let uu____23676 =
                  let uu____23677 = FStar_Util.message_of_exn uu___347_23669
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23677
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____23676)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____23671);
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
                   let uu____23722 =
                     let uu____23723 =
                       let uu____23730 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____23730)  in
                     FStar_Syntax_Syntax.Tm_refine uu____23723  in
                   mk uu____23722 t01.FStar_Syntax_Syntax.pos
               | uu____23735 -> t2)
          | uu____23736 -> t2  in
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
        let uu____23817 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____23817 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____23854 ->
                 let uu____23863 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____23863 with
                  | (actuals,uu____23873,uu____23874) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____23892 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____23892 with
                         | (binders,args) ->
                             let uu____23903 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____23903
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
      | uu____23917 ->
          let uu____23918 = FStar_Syntax_Util.head_and_args t  in
          (match uu____23918 with
           | (head1,args) ->
               let uu____23961 =
                 let uu____23962 = FStar_Syntax_Subst.compress head1  in
                 uu____23962.FStar_Syntax_Syntax.n  in
               (match uu____23961 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____23983 =
                      let uu____23998 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____23998  in
                    (match uu____23983 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____24036 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___349_24044 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___349_24044.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___349_24044.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___349_24044.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___349_24044.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___349_24044.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___349_24044.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___349_24044.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___349_24044.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___349_24044.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___349_24044.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___349_24044.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___349_24044.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___349_24044.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___349_24044.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___349_24044.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___349_24044.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___349_24044.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___349_24044.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___349_24044.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___349_24044.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___349_24044.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___349_24044.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___349_24044.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___349_24044.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___349_24044.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___349_24044.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___349_24044.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___349_24044.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___349_24044.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___349_24044.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___349_24044.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___349_24044.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___349_24044.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___349_24044.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___349_24044.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___349_24044.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___349_24044.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___349_24044.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___349_24044.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___349_24044.FStar_TypeChecker_Env.nbe)
                                 }) t
                               in
                            match uu____24036 with
                            | (uu____24045,ty,uu____24047) ->
                                eta_expand_with_type env t ty))
                | uu____24048 ->
                    let uu____24049 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___350_24057 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___350_24057.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___350_24057.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___350_24057.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___350_24057.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___350_24057.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___350_24057.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___350_24057.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___350_24057.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___350_24057.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___350_24057.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___350_24057.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___350_24057.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___350_24057.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___350_24057.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___350_24057.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___350_24057.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___350_24057.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___350_24057.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___350_24057.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___350_24057.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___350_24057.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___350_24057.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___350_24057.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___350_24057.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___350_24057.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___350_24057.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___350_24057.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___350_24057.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___350_24057.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___350_24057.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___350_24057.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___350_24057.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___350_24057.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___350_24057.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___350_24057.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___350_24057.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___350_24057.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___350_24057.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___350_24057.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___350_24057.FStar_TypeChecker_Env.nbe)
                         }) t
                       in
                    (match uu____24049 with
                     | (uu____24058,ty,uu____24060) ->
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
      let uu___351_24141 = x  in
      let uu____24142 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___351_24141.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___351_24141.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____24142
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____24145 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____24168 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____24169 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____24170 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____24171 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____24178 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____24179 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____24180 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___352_24214 = rc  in
          let uu____24215 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____24224 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___352_24214.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____24215;
            FStar_Syntax_Syntax.residual_flags = uu____24224
          }  in
        let uu____24227 =
          let uu____24228 =
            let uu____24247 = elim_delayed_subst_binders bs  in
            let uu____24256 = elim_delayed_subst_term t2  in
            let uu____24259 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____24247, uu____24256, uu____24259)  in
          FStar_Syntax_Syntax.Tm_abs uu____24228  in
        mk1 uu____24227
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____24296 =
          let uu____24297 =
            let uu____24312 = elim_delayed_subst_binders bs  in
            let uu____24321 = elim_delayed_subst_comp c  in
            (uu____24312, uu____24321)  in
          FStar_Syntax_Syntax.Tm_arrow uu____24297  in
        mk1 uu____24296
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____24340 =
          let uu____24341 =
            let uu____24348 = elim_bv bv  in
            let uu____24349 = elim_delayed_subst_term phi  in
            (uu____24348, uu____24349)  in
          FStar_Syntax_Syntax.Tm_refine uu____24341  in
        mk1 uu____24340
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____24380 =
          let uu____24381 =
            let uu____24398 = elim_delayed_subst_term t2  in
            let uu____24401 = elim_delayed_subst_args args  in
            (uu____24398, uu____24401)  in
          FStar_Syntax_Syntax.Tm_app uu____24381  in
        mk1 uu____24380
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___353_24473 = p  in
              let uu____24474 =
                let uu____24475 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____24475  in
              {
                FStar_Syntax_Syntax.v = uu____24474;
                FStar_Syntax_Syntax.p =
                  (uu___353_24473.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___354_24477 = p  in
              let uu____24478 =
                let uu____24479 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____24479  in
              {
                FStar_Syntax_Syntax.v = uu____24478;
                FStar_Syntax_Syntax.p =
                  (uu___354_24477.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___355_24486 = p  in
              let uu____24487 =
                let uu____24488 =
                  let uu____24495 = elim_bv x  in
                  let uu____24496 = elim_delayed_subst_term t0  in
                  (uu____24495, uu____24496)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____24488  in
              {
                FStar_Syntax_Syntax.v = uu____24487;
                FStar_Syntax_Syntax.p =
                  (uu___355_24486.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___356_24519 = p  in
              let uu____24520 =
                let uu____24521 =
                  let uu____24534 =
                    FStar_List.map
                      (fun uu____24557  ->
                         match uu____24557 with
                         | (x,b) ->
                             let uu____24570 = elim_pat x  in
                             (uu____24570, b)) pats
                     in
                  (fv, uu____24534)  in
                FStar_Syntax_Syntax.Pat_cons uu____24521  in
              {
                FStar_Syntax_Syntax.v = uu____24520;
                FStar_Syntax_Syntax.p =
                  (uu___356_24519.FStar_Syntax_Syntax.p)
              }
          | uu____24583 -> p  in
        let elim_branch uu____24607 =
          match uu____24607 with
          | (pat,wopt,t3) ->
              let uu____24633 = elim_pat pat  in
              let uu____24636 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____24639 = elim_delayed_subst_term t3  in
              (uu____24633, uu____24636, uu____24639)
           in
        let uu____24644 =
          let uu____24645 =
            let uu____24668 = elim_delayed_subst_term t2  in
            let uu____24671 = FStar_List.map elim_branch branches  in
            (uu____24668, uu____24671)  in
          FStar_Syntax_Syntax.Tm_match uu____24645  in
        mk1 uu____24644
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____24802 =
          match uu____24802 with
          | (tc,topt) ->
              let uu____24837 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____24847 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____24847
                | FStar_Util.Inr c ->
                    let uu____24849 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____24849
                 in
              let uu____24850 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____24837, uu____24850)
           in
        let uu____24859 =
          let uu____24860 =
            let uu____24887 = elim_delayed_subst_term t2  in
            let uu____24890 = elim_ascription a  in
            (uu____24887, uu____24890, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____24860  in
        mk1 uu____24859
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___357_24951 = lb  in
          let uu____24952 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____24955 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___357_24951.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___357_24951.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____24952;
            FStar_Syntax_Syntax.lbeff =
              (uu___357_24951.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____24955;
            FStar_Syntax_Syntax.lbattrs =
              (uu___357_24951.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___357_24951.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____24958 =
          let uu____24959 =
            let uu____24972 =
              let uu____24979 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____24979)  in
            let uu____24988 = elim_delayed_subst_term t2  in
            (uu____24972, uu____24988)  in
          FStar_Syntax_Syntax.Tm_let uu____24959  in
        mk1 uu____24958
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____25032 =
          let uu____25033 =
            let uu____25040 = elim_delayed_subst_term tm  in
            (uu____25040, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____25033  in
        mk1 uu____25032
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____25051 =
          let uu____25052 =
            let uu____25059 = elim_delayed_subst_term t2  in
            let uu____25062 = elim_delayed_subst_meta md  in
            (uu____25059, uu____25062)  in
          FStar_Syntax_Syntax.Tm_meta uu____25052  in
        mk1 uu____25051

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___270_25071  ->
         match uu___270_25071 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____25075 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____25075
         | f -> f) flags1

and (elim_delayed_subst_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun c  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        c.FStar_Syntax_Syntax.pos
       in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uopt) ->
        let uu____25098 =
          let uu____25099 =
            let uu____25108 = elim_delayed_subst_term t  in
            (uu____25108, uopt)  in
          FStar_Syntax_Syntax.Total uu____25099  in
        mk1 uu____25098
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____25125 =
          let uu____25126 =
            let uu____25135 = elim_delayed_subst_term t  in
            (uu____25135, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____25126  in
        mk1 uu____25125
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___358_25144 = ct  in
          let uu____25145 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____25148 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____25159 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___358_25144.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___358_25144.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____25145;
            FStar_Syntax_Syntax.effect_args = uu____25148;
            FStar_Syntax_Syntax.flags = uu____25159
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___271_25162  ->
    match uu___271_25162 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____25176 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____25176
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____25215 =
          let uu____25222 = elim_delayed_subst_term t  in (m, uu____25222)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____25215
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____25234 =
          let uu____25243 = elim_delayed_subst_term t  in
          (m1, m2, uu____25243)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____25234
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                          FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.arg_qualifier
                                                            FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____25276  ->
         match uu____25276 with
         | (t,q) ->
             let uu____25295 = elim_delayed_subst_term t  in (uu____25295, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____25323  ->
         match uu____25323 with
         | (x,q) ->
             let uu____25342 =
               let uu___359_25343 = x  in
               let uu____25344 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___359_25343.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___359_25343.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____25344
               }  in
             (uu____25342, q)) bs

let (elim_uvars_aux_tc :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.comp) FStar_Util.either
          ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                                                    FStar_Pervasives_Native.option)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,(FStar_Syntax_Syntax.term'
                                                          FStar_Syntax_Syntax.syntax,
                                                         FStar_Syntax_Syntax.comp'
                                                           FStar_Syntax_Syntax.syntax)
                                                         FStar_Util.either)
            FStar_Pervasives_Native.tuple3)
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
            | (uu____25450,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____25482,FStar_Util.Inl t) ->
                let uu____25504 =
                  let uu____25511 =
                    let uu____25512 =
                      let uu____25527 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____25527)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____25512  in
                  FStar_Syntax_Syntax.mk uu____25511  in
                uu____25504 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____25543 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____25543 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____25575 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____25648 ->
                    let uu____25649 =
                      let uu____25658 =
                        let uu____25659 = FStar_Syntax_Subst.compress t4  in
                        uu____25659.FStar_Syntax_Syntax.n  in
                      (uu____25658, tc)  in
                    (match uu____25649 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____25688) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____25735) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____25780,FStar_Util.Inl uu____25781) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____25812 -> failwith "Impossible")
                 in
              (match uu____25575 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
  
let (elim_uvars_aux_t :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                                                    FStar_Pervasives_Native.option)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.term'
                                                         FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____25949 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____25949 with
          | (univ_names1,binders1,tc) ->
              let uu____26023 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____26023)
  
let (elim_uvars_aux_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                                                    FStar_Pervasives_Native.option)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.comp'
                                                         FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
          let uu____26076 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____26076 with
          | (univ_names1,binders1,tc) ->
              let uu____26150 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____26150)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____26191 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____26191 with
           | (univ_names1,binders1,typ1) ->
               let uu___360_26231 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___360_26231.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___360_26231.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___360_26231.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___360_26231.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___361_26246 = s  in
          let uu____26247 =
            let uu____26248 =
              let uu____26257 = FStar_List.map (elim_uvars env) sigs  in
              (uu____26257, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____26248  in
          {
            FStar_Syntax_Syntax.sigel = uu____26247;
            FStar_Syntax_Syntax.sigrng =
              (uu___361_26246.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___361_26246.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___361_26246.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___361_26246.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____26274 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____26274 with
           | (univ_names1,uu____26298,typ1) ->
               let uu___362_26320 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___362_26320.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___362_26320.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___362_26320.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___362_26320.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____26326 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____26326 with
           | (univ_names1,uu____26350,typ1) ->
               let uu___363_26372 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___363_26372.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___363_26372.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___363_26372.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___363_26372.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____26400 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____26400 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____26425 =
                            let uu____26426 =
                              let uu____26427 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____26427  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____26426
                             in
                          elim_delayed_subst_term uu____26425  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___364_26430 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___364_26430.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___364_26430.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___364_26430.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___364_26430.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___365_26431 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___365_26431.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___365_26431.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___365_26431.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___365_26431.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___366_26437 = s  in
          let uu____26438 =
            let uu____26439 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____26439  in
          {
            FStar_Syntax_Syntax.sigel = uu____26438;
            FStar_Syntax_Syntax.sigrng =
              (uu___366_26437.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___366_26437.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___366_26437.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___366_26437.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____26443 = elim_uvars_aux_t env us [] t  in
          (match uu____26443 with
           | (us1,uu____26467,t1) ->
               let uu___367_26489 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___367_26489.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___367_26489.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___367_26489.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___367_26489.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____26490 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____26492 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____26492 with
           | (univs1,binders,signature) ->
               let uu____26532 =
                 let uu____26537 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____26537 with
                 | (univs_opening,univs2) ->
                     let uu____26560 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____26560)
                  in
               (match uu____26532 with
                | (univs_opening,univs_closing) ->
                    let uu____26563 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____26569 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____26570 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____26569, uu____26570)  in
                    (match uu____26563 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____26596 =
                           match uu____26596 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____26614 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____26614 with
                                | (us1,t1) ->
                                    let uu____26625 =
                                      let uu____26634 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____26645 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____26634, uu____26645)  in
                                    (match uu____26625 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____26674 =
                                           let uu____26683 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____26694 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____26683, uu____26694)  in
                                         (match uu____26674 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____26724 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____26724
                                                 in
                                              let uu____26725 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____26725 with
                                               | (uu____26752,uu____26753,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____26776 =
                                                       let uu____26777 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____26777
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____26776
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____26786 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____26786 with
                           | (uu____26805,uu____26806,t1) -> t1  in
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
                             | uu____26882 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____26909 =
                               let uu____26910 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____26910.FStar_Syntax_Syntax.n  in
                             match uu____26909 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____26969 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____27002 =
                               let uu____27003 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____27003.FStar_Syntax_Syntax.n  in
                             match uu____27002 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____27026) ->
                                 let uu____27051 = destruct_action_body body
                                    in
                                 (match uu____27051 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____27100 ->
                                 let uu____27101 = destruct_action_body t  in
                                 (match uu____27101 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____27156 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____27156 with
                           | (action_univs,t) ->
                               let uu____27165 = destruct_action_typ_templ t
                                  in
                               (match uu____27165 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___368_27212 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___368_27212.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___368_27212.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___369_27214 = ed  in
                           let uu____27215 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____27216 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____27217 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____27218 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____27219 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____27220 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____27221 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____27222 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____27223 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____27224 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____27225 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____27226 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____27227 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____27228 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___369_27214.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___369_27214.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____27215;
                             FStar_Syntax_Syntax.bind_wp = uu____27216;
                             FStar_Syntax_Syntax.if_then_else = uu____27217;
                             FStar_Syntax_Syntax.ite_wp = uu____27218;
                             FStar_Syntax_Syntax.stronger = uu____27219;
                             FStar_Syntax_Syntax.close_wp = uu____27220;
                             FStar_Syntax_Syntax.assert_p = uu____27221;
                             FStar_Syntax_Syntax.assume_p = uu____27222;
                             FStar_Syntax_Syntax.null_wp = uu____27223;
                             FStar_Syntax_Syntax.trivial = uu____27224;
                             FStar_Syntax_Syntax.repr = uu____27225;
                             FStar_Syntax_Syntax.return_repr = uu____27226;
                             FStar_Syntax_Syntax.bind_repr = uu____27227;
                             FStar_Syntax_Syntax.actions = uu____27228;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___369_27214.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___370_27231 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___370_27231.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___370_27231.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___370_27231.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___370_27231.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___272_27252 =
            match uu___272_27252 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____27283 = elim_uvars_aux_t env us [] t  in
                (match uu____27283 with
                 | (us1,uu____27315,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___371_27346 = sub_eff  in
            let uu____27347 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____27350 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___371_27346.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___371_27346.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____27347;
              FStar_Syntax_Syntax.lift = uu____27350
            }  in
          let uu___372_27353 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___372_27353.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___372_27353.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___372_27353.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___372_27353.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____27363 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____27363 with
           | (univ_names1,binders1,comp1) ->
               let uu___373_27403 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___373_27403.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___373_27403.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___373_27403.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___373_27403.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____27406 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____27407 -> s
  
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
        let uu____27454 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____27454 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____27476 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____27476 with
             | (uu____27483,head_def) ->
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
      let uu____27489 = FStar_Syntax_Util.head_and_args t  in
      match uu____27489 with
      | (head1,args) ->
          let uu____27534 =
            let uu____27535 = FStar_Syntax_Subst.compress head1  in
            uu____27535.FStar_Syntax_Syntax.n  in
          (match uu____27534 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____27542;
                  FStar_Syntax_Syntax.vars = uu____27543;_},us)
               -> aux fv us args
           | uu____27549 -> FStar_Pervasives_Native.None)
  