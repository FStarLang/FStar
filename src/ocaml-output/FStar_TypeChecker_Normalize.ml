open Prims
let cases :
  'Auu____11 'Auu____12 .
    ('Auu____11 -> 'Auu____12) ->
      'Auu____12 -> 'Auu____11 FStar_Pervasives_Native.option -> 'Auu____12
  =
  fun f  ->
    fun d  ->
      fun uu___249_32  ->
        match uu___249_32 with
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
  fun uu___250_1097  ->
    match uu___250_1097 with
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
  fun uu___251_1159  ->
    match uu___251_1159 with
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
  fun uu___252_1249  ->
    match uu___252_1249 with | [] -> true | uu____1252 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        (fun uu___270_1283  ->
           match () with
           | () ->
               let uu____1284 =
                 FStar_List.nth env x.FStar_Syntax_Syntax.index  in
               FStar_Pervasives_Native.snd uu____1284) ()
      with
      | uu___269_1301 ->
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
                 (fun uu___272_1463  ->
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
            (fun uu____1740  ->
               let uu____1741 = FStar_Syntax_Print.tag_of_term t  in
               let uu____1742 = env_to_string env  in
               let uu____1743 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____1741 uu____1742 uu____1743);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____1752 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____1755 ->
                    let uu____1778 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____1778
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____1779 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____1780 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____1781 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____1782 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____1806 ->
                           let uu____1819 =
                             let uu____1820 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____1821 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____1820 uu____1821
                              in
                           failwith uu____1819
                       | uu____1824 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___253_1859  ->
                                         match uu___253_1859 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____1866 =
                                               let uu____1873 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____1873)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____1866
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___273_1883 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___273_1883.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___273_1883.FStar_Syntax_Syntax.sort)
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
                                              | uu____1888 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____1891 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___274_1895 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___274_1895.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___274_1895.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____1916 =
                        let uu____1917 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____1917  in
                      mk uu____1916 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____1925 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1925  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____1927 = lookup_bvar env x  in
                    (match uu____1927 with
                     | Univ uu____1930 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___275_1934 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___275_1934.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___275_1934.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____1940,uu____1941) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____2030  ->
                              fun stack1  ->
                                match uu____2030 with
                                | (a,aq) ->
                                    let uu____2042 =
                                      let uu____2043 =
                                        let uu____2050 =
                                          let uu____2051 =
                                            let uu____2082 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____2082, false)  in
                                          Clos uu____2051  in
                                        (uu____2050, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____2043  in
                                    uu____2042 :: stack1) args)
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
                    let uu____2270 = close_binders cfg env bs  in
                    (match uu____2270 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____2325 =
                      let uu____2338 =
                        let uu____2347 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____2347]  in
                      close_binders cfg env uu____2338  in
                    (match uu____2325 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____2392 =
                             let uu____2393 =
                               let uu____2400 =
                                 let uu____2401 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____2401
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____2400, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____2393  in
                           mk uu____2392 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____2500 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____2500
                      | FStar_Util.Inr c ->
                          let uu____2514 = close_comp cfg env c  in
                          FStar_Util.Inr uu____2514
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____2533 =
                        let uu____2534 =
                          let uu____2561 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____2561, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____2534  in
                      mk uu____2533 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____2607 =
                            let uu____2608 =
                              let uu____2615 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____2615, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____2608  in
                          mk uu____2607 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____2667  -> dummy :: env1) env
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
                    let uu____2688 =
                      let uu____2699 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____2699
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____2718 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___276_2734 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___276_2734.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___276_2734.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____2718))
                       in
                    (match uu____2688 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___277_2752 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___277_2752.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___277_2752.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___277_2752.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___277_2752.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____2766,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____2829  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____2846 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____2846
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____2858  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____2882 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____2882
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___278_2890 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___278_2890.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___278_2890.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___279_2891 = lb  in
                      let uu____2892 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___279_2891.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___279_2891.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____2892;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___279_2891.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___279_2891.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____2924  -> fun env1  -> dummy :: env1)
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
            (fun uu____3013  ->
               let uu____3014 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3015 = env_to_string env  in
               let uu____3016 = stack_to_string stack  in
               let uu____3017 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____3014 uu____3015 uu____3016 uu____3017);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____3022,uu____3023),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____3102 = close_binders cfg env' bs  in
               (match uu____3102 with
                | (bs1,uu____3118) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____3138 =
                      let uu___280_3141 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___280_3141.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___280_3141.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____3138)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____3197 =
                 match uu____3197 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____3312 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____3341 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____3425  ->
                                     fun uu____3426  ->
                                       match (uu____3425, uu____3426) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____3565 = norm_pat env4 p1
                                              in
                                           (match uu____3565 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____3341 with
                            | (pats1,env4) ->
                                ((let uu___281_3727 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___281_3727.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___282_3746 = x  in
                             let uu____3747 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___282_3746.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___282_3746.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3747
                             }  in
                           ((let uu___283_3761 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___283_3761.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___284_3772 = x  in
                             let uu____3773 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___284_3772.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___284_3772.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3773
                             }  in
                           ((let uu___285_3787 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___285_3787.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___286_3803 = x  in
                             let uu____3804 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___286_3803.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___286_3803.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3804
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___287_3821 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___287_3821.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____3826 = norm_pat env2 pat  in
                     (match uu____3826 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____3895 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____3895
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____3914 =
                   let uu____3915 =
                     let uu____3938 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____3938)  in
                   FStar_Syntax_Syntax.Tm_match uu____3915  in
                 mk uu____3914 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____4053 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____4162  ->
                                       match uu____4162 with
                                       | (a,q) ->
                                           let uu____4189 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____4189, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____4053
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____4202 =
                       let uu____4209 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____4209)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____4202
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____4221 =
                       let uu____4230 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____4230)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____4221
                 | uu____4235 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____4241 -> failwith "Impossible: unexpected stack element")

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
        let uu____4257 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4340  ->
                  fun uu____4341  ->
                    match (uu____4340, uu____4341) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___288_4481 = b  in
                          let uu____4482 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___288_4481.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___288_4481.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4482
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____4257 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____4619 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4632 = inline_closure_env cfg env [] t  in
                 let uu____4633 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____4632 uu____4633
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4646 = inline_closure_env cfg env [] t  in
                 let uu____4647 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4646 uu____4647
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____4701  ->
                           match uu____4701 with
                           | (a,q) ->
                               let uu____4722 =
                                 inline_closure_env cfg env [] a  in
                               (uu____4722, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___254_4739  ->
                           match uu___254_4739 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4743 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____4743
                           | f -> f))
                    in
                 let uu____4747 =
                   let uu___289_4748 = c1  in
                   let uu____4749 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4749;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___289_4748.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____4747)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___255_4759  ->
            match uu___255_4759 with
            | FStar_Syntax_Syntax.DECREASES uu____4760 -> false
            | uu____4763 -> true))

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
                   (fun uu___256_4781  ->
                      match uu___256_4781 with
                      | FStar_Syntax_Syntax.DECREASES uu____4782 -> false
                      | uu____4785 -> true))
               in
            let rc1 =
              let uu___290_4787 = rc  in
              let uu____4788 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___290_4787.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4788;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____4797 -> lopt

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
    let uu____4864 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____4864 with
    | FStar_Pervasives_Native.Some e ->
        let uu____4903 = FStar_Syntax_Embeddings.unembed e t  in
        uu____4903 true FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____4923 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____4923) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____4985  ->
           fun subst1  ->
             match uu____4985 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____5026,uu____5027)) ->
                      let uu____5086 = b  in
                      (match uu____5086 with
                       | (bv,uu____5094) ->
                           let uu____5095 =
                             let uu____5096 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____5096  in
                           if uu____5095
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____5101 = unembed_binder term1  in
                              match uu____5101 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____5108 =
                                      let uu___291_5109 = bv  in
                                      let uu____5110 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___291_5109.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___291_5109.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____5110
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____5108
                                     in
                                  let b_for_x =
                                    let uu____5116 =
                                      let uu____5123 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____5123)
                                       in
                                    FStar_Syntax_Syntax.NT uu____5116  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___257_5139  ->
                                         match uu___257_5139 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____5140,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____5142;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____5143;_})
                                             ->
                                             let uu____5148 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____5148
                                         | uu____5149 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____5150 -> subst1)) env []
  
let reduce_primops :
  'Auu____5172 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv,'Auu____5172) FStar_Pervasives_Native.tuple2
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
            (let uu____5224 = FStar_Syntax_Util.head_and_args tm  in
             match uu____5224 with
             | (head1,args) ->
                 let uu____5269 =
                   let uu____5270 = FStar_Syntax_Util.un_uinst head1  in
                   uu____5270.FStar_Syntax_Syntax.n  in
                 (match uu____5269 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____5276 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                      (match uu____5276 with
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
                                (fun uu____5304  ->
                                   let uu____5305 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name
                                      in
                                   let uu____5306 =
                                     FStar_Util.string_of_int l  in
                                   let uu____5313 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____5305 uu____5306 uu____5313);
                              tm)
                           else
                             (let uu____5315 =
                                if l = prim_step.FStar_TypeChecker_Cfg.arity
                                then (args, [])
                                else
                                  FStar_List.splitAt
                                    prim_step.FStar_TypeChecker_Cfg.arity
                                    args
                                 in
                              match uu____5315 with
                              | (args_1,args_2) ->
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____5452  ->
                                        let uu____5453 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____5453);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____5456  ->
                                             if
                                               prim_step.FStar_TypeChecker_Cfg.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____5458 =
                                      prim_step.FStar_TypeChecker_Cfg.interpretation
                                        psc norm_cb args_1
                                       in
                                    match uu____5458 with
                                    | FStar_Pervasives_Native.None  ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5468  ->
                                              let uu____5469 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____5469);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5475  ->
                                              let uu____5476 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____5477 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____5476 uu____5477);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____5478 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____5482  ->
                                 let uu____5483 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____5483);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5487  ->
                            let uu____5488 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5488);
                       (match args with
                        | (a1,uu____5492)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____5517 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5531  ->
                            let uu____5532 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5532);
                       (match args with
                        | (t,uu____5536)::(r,uu____5538)::[] ->
                            let uu____5579 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____5579 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____5585 -> tm))
                  | uu____5596 -> tm))
  
let reduce_equality :
  'Auu____5607 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv,'Auu____5607) FStar_Pervasives_Native.tuple2
           FStar_Pervasives_Native.option,closure)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun tm  ->
        reduce_primops norm_cb
          (let uu___292_5660 = cfg  in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___293_5663 = FStar_TypeChecker_Cfg.default_steps  in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___293_5663.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___293_5663.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___293_5663.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___293_5663.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___293_5663.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___293_5663.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___293_5663.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___293_5663.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___293_5663.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___293_5663.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___293_5663.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___293_5663.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___293_5663.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___293_5663.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___293_5663.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___293_5663.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___293_5663.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___293_5663.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___293_5663.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___293_5663.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___293_5663.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___293_5663.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___293_5663.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___293_5663.FStar_TypeChecker_Cfg.nbe_step)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___292_5660.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___292_5660.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___292_5660.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___292_5660.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___292_5660.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___292_5660.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___292_5660.FStar_TypeChecker_Cfg.reifying)
           }) tm
  
let is_norm_request :
  'Auu____5670 .
    FStar_Syntax_Syntax.term -> 'Auu____5670 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____5685 =
        let uu____5692 =
          let uu____5693 = FStar_Syntax_Util.un_uinst hd1  in
          uu____5693.FStar_Syntax_Syntax.n  in
        (uu____5692, args)  in
      match uu____5685 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5699::uu____5700::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5704::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____5709::uu____5710::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____5713 -> false
  
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s  ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
  
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___258_5735  ->
    match uu___258_5735 with
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
        let uu____5741 =
          let uu____5744 =
            let uu____5745 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldOnly uu____5745  in
          [uu____5744]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____5741
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____5751 =
          let uu____5754 =
            let uu____5755 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldFully uu____5755  in
          [uu____5754]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____5751
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.UnfoldAttr t]
    | FStar_Syntax_Embeddings.NBE  -> [FStar_TypeChecker_Env.NBE]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  = fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____5778 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term,'Auu____5778)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____5829 =
            let uu____5834 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____5834 s  in
          match uu____5829 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____5850 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____5850
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
        | uu____5876::(tm,uu____5878)::[] ->
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
        | (tm,uu____5907)::[] ->
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
        | (steps,uu____5928)::uu____5929::(tm,uu____5931)::[] ->
            let add_exclude s z =
              let uu____5969 =
                FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s  in
              if uu____5969
              then s
              else (FStar_TypeChecker_Env.Exclude z) :: s  in
            let uu____5973 =
              let uu____5978 = full_norm steps  in parse_steps uu____5978  in
            (match uu____5973 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = FStar_TypeChecker_Env.Beta :: s  in
                 let s2 = add_exclude s1 FStar_TypeChecker_Env.Zeta  in
                 let s3 = add_exclude s2 FStar_TypeChecker_Env.Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____6017 -> FStar_Pervasives_Native.None
  
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun s  ->
      fun tm  ->
        let delta_level =
          let uu____6048 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___259_6053  ->
                    match uu___259_6053 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____6054 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____6055 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____6058 -> true
                    | uu____6061 -> false))
             in
          if uu____6048
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta]  in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____6068  ->
             let uu____6069 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____6069);
        (let tm_norm =
           let uu____6071 =
             let uu____6086 = FStar_TypeChecker_Cfg.cfg_env cfg  in
             uu____6086.FStar_TypeChecker_Env.nbe  in
           uu____6071 s cfg.FStar_TypeChecker_Cfg.tcenv tm  in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____6090  ->
              let uu____6091 = FStar_Syntax_Print.term_to_string tm_norm  in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____6091);
         tm_norm)
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___260_6098  ->
    match uu___260_6098 with
    | (App
        (uu____6101,{
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reify );
                      FStar_Syntax_Syntax.pos = uu____6102;
                      FStar_Syntax_Syntax.vars = uu____6103;_},uu____6104,uu____6105))::uu____6106
        -> true
    | uu____6111 -> false
  
let firstn :
  'Auu____6120 .
    Prims.int ->
      'Auu____6120 Prims.list ->
        ('Auu____6120 Prims.list,'Auu____6120 Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack  ->
      match stack with
      | (App
          (uu____6162,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____6163;
                        FStar_Syntax_Syntax.vars = uu____6164;_},uu____6165,uu____6166))::uu____6167
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____6172 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____6195) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____6205) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____6226  ->
                  match uu____6226 with
                  | (a,uu____6236) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6246 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____6269 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____6270 -> false
    | FStar_Syntax_Syntax.Tm_type uu____6283 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____6284 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____6285 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____6286 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____6287 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____6288 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____6295 -> false
    | FStar_Syntax_Syntax.Tm_let uu____6302 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____6315 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____6334 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____6349 -> true
    | FStar_Syntax_Syntax.Tm_match uu____6356 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____6426  ->
                   match uu____6426 with
                   | (a,uu____6436) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____6447) ->
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
                     (fun uu____6575  ->
                        match uu____6575 with
                        | (a,uu____6585) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____6594,uu____6595,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____6601,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____6607 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____6614 -> false
            | FStar_Syntax_Syntax.Meta_named uu____6615 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____6621 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____6627 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_fully  -> true | uu____6633 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_reify  -> true | uu____6639 -> false
  
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
            let uu____6668 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
            match uu____6668 with
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
              (fun uu____6796  ->
                 fun uu____6797  ->
                   match (uu____6796, uu____6797) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____6857 =
            match uu____6857 with
            | (x,y,z) ->
                let uu____6867 = FStar_Util.string_of_bool x  in
                let uu____6868 = FStar_Util.string_of_bool y  in
                let uu____6869 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____6867 uu____6868
                  uu____6869
             in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg  in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____6888  ->
                    let uu____6889 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____6890 = FStar_Util.string_of_bool b  in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____6889 uu____6890);
               if b then reif else no)
            else
              if
                (let uu____6898 = FStar_TypeChecker_Cfg.find_prim_step cfg fv
                    in
                 FStar_Option.isSome uu____6898)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____6903  ->
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
                          ((is_rec,uu____6937),uu____6938);
                        FStar_Syntax_Syntax.sigrng = uu____6939;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____6941;
                        FStar_Syntax_Syntax.sigattrs = uu____6942;_},uu____6943),uu____6944),uu____6945,uu____6946,uu____6947)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7052  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____7053,uu____7054,uu____7055,uu____7056) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7123  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____7125),uu____7126);
                        FStar_Syntax_Syntax.sigrng = uu____7127;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7129;
                        FStar_Syntax_Syntax.sigattrs = uu____7130;_},uu____7131),uu____7132),uu____7133,uu____7134,uu____7135)
                     when
                     is_rec &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7240  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____7241,FStar_Pervasives_Native.Some
                    uu____7242,uu____7243,uu____7244) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7312  ->
                           let uu____7313 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____7313);
                      (let uu____7314 =
                         let uu____7323 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____7343 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____7343
                            in
                         let uu____7350 =
                           let uu____7359 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____7379 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____7379
                              in
                           let uu____7388 =
                             let uu____7397 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____7417 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____7417
                                in
                             [uu____7397]  in
                           uu____7359 :: uu____7388  in
                         uu____7323 :: uu____7350  in
                       comb_or uu____7314))
                 | (uu____7448,uu____7449,FStar_Pervasives_Native.Some
                    uu____7450,uu____7451) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7519  ->
                           let uu____7520 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____7520);
                      (let uu____7521 =
                         let uu____7530 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____7550 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____7550
                            in
                         let uu____7557 =
                           let uu____7566 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____7586 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____7586
                              in
                           let uu____7595 =
                             let uu____7604 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____7624 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____7624
                                in
                             [uu____7604]  in
                           uu____7566 :: uu____7595  in
                         uu____7530 :: uu____7557  in
                       comb_or uu____7521))
                 | (uu____7655,uu____7656,uu____7657,FStar_Pervasives_Native.Some
                    uu____7658) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7726  ->
                           let uu____7727 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____7727);
                      (let uu____7728 =
                         let uu____7737 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____7757 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____7757
                            in
                         let uu____7764 =
                           let uu____7773 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____7793 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____7793
                              in
                           let uu____7802 =
                             let uu____7811 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____7831 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____7831
                                in
                             [uu____7811]  in
                           uu____7773 :: uu____7802  in
                         uu____7737 :: uu____7764  in
                       comb_or uu____7728))
                 | uu____7862 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7908  ->
                           let uu____7909 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____7910 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____7911 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level
                              in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____7909 uu____7910 uu____7911);
                      (let uu____7912 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___261_7916  ->
                                 match uu___261_7916 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.InliningDelta  ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       fv.FStar_Syntax_Syntax.fv_delta l))
                          in
                       FStar_All.pipe_left yesno uu____7912)))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____7929  ->
               let uu____7930 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____7931 =
                 let uu____7932 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____7932  in
               let uu____7933 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____7930 uu____7931 uu____7933);
          (match res with
           | (false ,uu____7934,uu____7935) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____7936 ->
               let uu____7943 =
                 let uu____7944 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____7944
                  in
               FStar_All.pipe_left failwith uu____7943)
  
let decide_unfolding :
  'Auu____7961 'Auu____7962 .
    FStar_TypeChecker_Cfg.cfg ->
      'Auu____7961 ->
        stack_elt Prims.list ->
          'Auu____7962 ->
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
                    let uu___294_8031 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___295_8034 = cfg.FStar_TypeChecker_Cfg.steps
                            in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___295_8034.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___295_8034.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___295_8034.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___295_8034.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___295_8034.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___295_8034.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___295_8034.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___295_8034.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___295_8034.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___295_8034.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___295_8034.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___295_8034.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___295_8034.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___295_8034.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___295_8034.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___295_8034.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___295_8034.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___295_8034.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___295_8034.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___295_8034.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___295_8034.FStar_TypeChecker_Cfg.nbe_step)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___294_8031.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___294_8031.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___294_8031.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___294_8031.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___294_8031.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___294_8031.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___294_8031.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___294_8031.FStar_TypeChecker_Cfg.reifying)
                    }  in
                  let stack' = (Cfg cfg) :: stack  in
                  FStar_Pervasives_Native.Some (cfg', stack')
              | Should_unfold_reify  ->
                  let uu____8052 =
                    let uu____8059 = FStar_List.tl stack  in
                    (cfg, uu____8059)  in
                  FStar_Pervasives_Native.Some uu____8052
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____8346 ->
                   let uu____8369 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____8369
               | uu____8370 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____8379  ->
               let uu____8380 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____8381 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____8382 = FStar_Syntax_Print.term_to_string t1  in
               let uu____8383 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____8390 =
                 let uu____8391 =
                   let uu____8394 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8394
                    in
                 stack_to_string uu____8391  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____8380 uu____8381 uu____8382 uu____8383 uu____8390);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____8420  ->
               let uu____8421 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____8421);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8425  ->
                     let uu____8426 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8426);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____8427 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8431  ->
                     let uu____8432 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8432);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____8433 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8437  ->
                     let uu____8438 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8438);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____8439 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8443  ->
                     let uu____8444 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8444);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8445;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_17;
                 FStar_Syntax_Syntax.fv_qual = uu____8446;_}
               when _0_17 = (Prims.parse_int "0") ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8452  ->
                     let uu____8453 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8453);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8454;
                 FStar_Syntax_Syntax.fv_delta = uu____8455;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8459  ->
                     let uu____8460 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8460);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8461;
                 FStar_Syntax_Syntax.fv_delta = uu____8462;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____8463);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8473  ->
                     let uu____8474 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8474);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____8477 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv uu____8477
                  in
               let uu____8478 =
                 decide_unfolding cfg env stack t1.FStar_Syntax_Syntax.pos fv
                   qninfo
                  in
               (match uu____8478 with
                | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                    do_unfold_fv cfg1 env stack1 t1 qninfo fv
                | FStar_Pervasives_Native.None  -> rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_quoted uu____8505 ->
               let uu____8512 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____8512
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
                  && (is_norm_request hd1 args))
                 &&
                 (let uu____8548 =
                    FStar_Ident.lid_equals
                      (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____8548)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___296_8552 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___297_8555 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___297_8555.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___297_8555.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___297_8555.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___297_8555.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___297_8555.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___297_8555.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___297_8555.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___297_8555.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___297_8555.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___297_8555.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___297_8555.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___297_8555.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___297_8555.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___297_8555.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___297_8555.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___297_8555.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___297_8555.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___297_8555.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___297_8555.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___297_8555.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___297_8555.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___297_8555.FStar_TypeChecker_Cfg.nbe_step)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___296_8552.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___296_8552.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___296_8552.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___296_8552.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___296_8552.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___296_8552.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____8560 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____8560 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____8593  ->
                                 fun stack1  ->
                                   match uu____8593 with
                                   | (a,aq) ->
                                       let uu____8605 =
                                         let uu____8606 =
                                           let uu____8613 =
                                             let uu____8614 =
                                               let uu____8645 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____8645, false)
                                                in
                                             Clos uu____8614  in
                                           (uu____8613, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____8606  in
                                       uu____8605 :: stack1) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____8733  ->
                            let uu____8734 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____8734);
                       norm cfg env stack1 hd1))
                 | FStar_Pervasives_Native.Some (s,tm) when is_nbe_request s
                     ->
                     let tm' = closure_as_term cfg env tm  in
                     let tm_norm = nbe_eval cfg s tm'  in
                     norm cfg env stack tm_norm
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____8770 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting norm request on %s ... \n" uu____8770)
                      else ();
                      (let delta_level =
                         let uu____8775 =
                           FStar_All.pipe_right s
                             (FStar_Util.for_some
                                (fun uu___262_8780  ->
                                   match uu___262_8780 with
                                   | FStar_TypeChecker_Env.UnfoldUntil
                                       uu____8781 -> true
                                   | FStar_TypeChecker_Env.UnfoldOnly
                                       uu____8782 -> true
                                   | FStar_TypeChecker_Env.UnfoldFully
                                       uu____8785 -> true
                                   | uu____8788 -> false))
                            in
                         if uu____8775
                         then
                           [FStar_TypeChecker_Env.Unfold
                              FStar_Syntax_Syntax.delta_constant]
                         else [FStar_TypeChecker_Env.NoDelta]  in
                       let cfg'1 =
                         let uu___298_8793 = cfg  in
                         let uu____8794 =
                           let uu___299_8795 =
                             FStar_TypeChecker_Cfg.to_fsteps s  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___299_8795.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___299_8795.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___299_8795.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak =
                               (uu___299_8795.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___299_8795.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___299_8795.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___299_8795.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___299_8795.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               (uu___299_8795.FStar_TypeChecker_Cfg.unfold_only);
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___299_8795.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___299_8795.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___299_8795.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___299_8795.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___299_8795.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___299_8795.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___299_8795.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___299_8795.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___299_8795.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___299_8795.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___299_8795.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___299_8795.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___299_8795.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               true;
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___299_8795.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___299_8795.FStar_TypeChecker_Cfg.nbe_step)
                           }  in
                         {
                           FStar_TypeChecker_Cfg.steps = uu____8794;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___298_8793.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___298_8793.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = delta_level;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___298_8793.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong =
                             (uu___298_8793.FStar_TypeChecker_Cfg.strong);
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___298_8793.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___298_8793.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let stack' =
                         let tail1 = (Cfg cfg) :: stack  in
                         if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           let uu____8800 =
                             let uu____8801 =
                               let uu____8806 = FStar_Util.now ()  in
                               (t1, uu____8806)  in
                             Debug uu____8801  in
                           uu____8800 :: tail1
                         else tail1  in
                       norm cfg'1 env stack' tm))))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____8810 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____8810
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____8819 =
                      let uu____8826 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____8826, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____8819  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____8835 = lookup_bvar env x  in
               (match uu____8835 with
                | Univ uu____8836 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                    then
                      let uu____8885 = FStar_ST.op_Bang r  in
                      (match uu____8885 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9003  ->
                                 let uu____9004 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____9005 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____9004
                                   uu____9005);
                            (let uu____9006 = maybe_weakly_reduced t'  in
                             if uu____9006
                             then
                               match stack with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____9007 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____9082)::uu____9083 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____9093,uu____9094))::stack_rest ->
                    (match c with
                     | Univ uu____9098 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____9107 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____9136  ->
                                    let uu____9137 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____9137);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____9171  ->
                                    let uu____9172 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____9172);
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
                       (fun uu____9240  ->
                          let uu____9241 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____9241);
                     norm cfg env stack1 t1)
                | (Match uu____9242)::uu____9243 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9256 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9256 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9292  -> dummy :: env1) env)
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
                                          let uu____9335 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9335)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___300_9342 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___300_9342.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___300_9342.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9343 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9349  ->
                                 let uu____9350 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9350);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___301_9361 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___301_9361.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___301_9361.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___301_9361.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___301_9361.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___301_9361.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___301_9361.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___301_9361.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___301_9361.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____9364)::uu____9365 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9374 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9374 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9410  -> dummy :: env1) env)
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
                                          let uu____9453 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9453)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___300_9460 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___300_9460.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___300_9460.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9461 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9467  ->
                                 let uu____9468 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9468);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___301_9479 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___301_9479.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___301_9479.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___301_9479.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___301_9479.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___301_9479.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___301_9479.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___301_9479.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___301_9479.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____9482)::uu____9483 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9494 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9494 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9530  -> dummy :: env1) env)
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
                                          let uu____9573 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9573)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___300_9580 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___300_9580.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___300_9580.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9581 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9587  ->
                                 let uu____9588 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9588);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___301_9599 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___301_9599.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___301_9599.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___301_9599.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___301_9599.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___301_9599.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___301_9599.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___301_9599.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___301_9599.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____9602)::uu____9603 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9616 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9616 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9652  -> dummy :: env1) env)
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
                                          let uu____9695 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9695)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___300_9702 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___300_9702.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___300_9702.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9703 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9709  ->
                                 let uu____9710 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9710);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___301_9721 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___301_9721.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___301_9721.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___301_9721.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___301_9721.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___301_9721.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___301_9721.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___301_9721.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___301_9721.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____9724)::uu____9725 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9738 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9738 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9774  -> dummy :: env1) env)
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
                                          let uu____9817 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9817)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___300_9824 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___300_9824.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___300_9824.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9825 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9831  ->
                                 let uu____9832 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9832);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___301_9843 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___301_9843.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___301_9843.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___301_9843.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___301_9843.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___301_9843.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___301_9843.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___301_9843.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___301_9843.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____9846)::uu____9847 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9864 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9864 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9900  -> dummy :: env1) env)
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
                                          let uu____9943 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9943)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___300_9950 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___300_9950.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___300_9950.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9951 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9957  ->
                                 let uu____9958 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9958);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___301_9969 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___301_9969.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___301_9969.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___301_9969.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___301_9969.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___301_9969.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___301_9969.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___301_9969.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___301_9969.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____9974 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9974 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10010  -> dummy :: env1) env)
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
                                          let uu____10053 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10053)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___300_10060 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___300_10060.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___300_10060.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10061 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10067  ->
                                 let uu____10068 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10068);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___301_10079 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___301_10079.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___301_10079.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___301_10079.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___301_10079.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___301_10079.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___301_10079.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___301_10079.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___301_10079.FStar_TypeChecker_Cfg.reifying)
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
                      (fun uu____10122  ->
                         fun stack1  ->
                           match uu____10122 with
                           | (a,aq) ->
                               let uu____10134 =
                                 let uu____10135 =
                                   let uu____10142 =
                                     let uu____10143 =
                                       let uu____10174 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____10174, false)  in
                                     Clos uu____10143  in
                                   (uu____10142, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____10135  in
                               uu____10134 :: stack1) args)
                  in
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____10262  ->
                     let uu____10263 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____10263);
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
                             ((let uu___302_10311 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___302_10311.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___302_10311.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____10312 ->
                      let uu____10327 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10327)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____10330 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____10330 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____10361 =
                          let uu____10362 =
                            let uu____10369 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___303_10375 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___303_10375.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___303_10375.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____10369)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____10362  in
                        mk uu____10361 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____10398 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____10398
               else
                 (let uu____10400 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____10400 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____10408 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____10434  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____10408 c1  in
                      let t2 =
                        let uu____10458 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____10458 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____10571)::uu____10572 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10585  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____10586)::uu____10587 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10598  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____10599,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____10600;
                                   FStar_Syntax_Syntax.vars = uu____10601;_},uu____10602,uu____10603))::uu____10604
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10611  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____10612)::uu____10613 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10624  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____10625 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10628  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____10632  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____10657 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____10657
                         | FStar_Util.Inr c ->
                             let uu____10671 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____10671
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____10694 =
                               let uu____10695 =
                                 let uu____10722 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____10722, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____10695
                                in
                             mk uu____10694 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____10757 ->
                           let uu____10758 =
                             let uu____10759 =
                               let uu____10760 =
                                 let uu____10787 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____10787, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____10760
                                in
                             mk uu____10759 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____10758))))
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
                   let uu___304_10864 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___305_10867 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___305_10867.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___305_10867.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___305_10867.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___305_10867.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___305_10867.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___305_10867.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___305_10867.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___305_10867.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___305_10867.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___305_10867.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___305_10867.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___305_10867.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___305_10867.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___305_10867.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___305_10867.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___305_10867.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___305_10867.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___305_10867.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___305_10867.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___305_10867.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___305_10867.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___305_10867.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___305_10867.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___305_10867.FStar_TypeChecker_Cfg.nbe_step)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___304_10864.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___304_10864.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___304_10864.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___304_10864.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___304_10864.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___304_10864.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___304_10864.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___304_10864.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____10903 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____10903 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___306_10923 = cfg  in
                               let uu____10924 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___306_10923.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____10924;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___306_10923.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___306_10923.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___306_10923.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___306_10923.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___306_10923.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___306_10923.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___306_10923.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____10931 =
                                 let uu____10932 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____10932  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____10931
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___307_10935 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___307_10935.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___307_10935.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___307_10935.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___307_10935.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____10936 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____10936
           | FStar_Syntax_Syntax.Tm_let
               ((uu____10947,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____10948;
                               FStar_Syntax_Syntax.lbunivs = uu____10949;
                               FStar_Syntax_Syntax.lbtyp = uu____10950;
                               FStar_Syntax_Syntax.lbeff = uu____10951;
                               FStar_Syntax_Syntax.lbdef = uu____10952;
                               FStar_Syntax_Syntax.lbattrs = uu____10953;
                               FStar_Syntax_Syntax.lbpos = uu____10954;_}::uu____10955),uu____10956)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name
                   cfg.FStar_TypeChecker_Cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____10996 =
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
               if uu____10996
               then
                 let binder =
                   let uu____10998 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____10998  in
                 let env1 =
                   let uu____11008 =
                     let uu____11015 =
                       let uu____11016 =
                         let uu____11047 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____11047,
                           false)
                          in
                       Clos uu____11016  in
                     ((FStar_Pervasives_Native.Some binder), uu____11015)  in
                   uu____11008 :: env  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____11142  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                 then
                   (FStar_TypeChecker_Cfg.log cfg
                      (fun uu____11146  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____11147 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____11147))
                 else
                   (let uu____11149 =
                      let uu____11154 =
                        let uu____11155 =
                          let uu____11162 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____11162
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____11155]  in
                      FStar_Syntax_Subst.open_term uu____11154 body  in
                    match uu____11149 with
                    | (bs,body1) ->
                        (FStar_TypeChecker_Cfg.log cfg
                           (fun uu____11189  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____11197 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____11197  in
                            FStar_Util.Inl
                              (let uu___308_11213 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___308_11213.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___308_11213.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____11216  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___309_11218 = lb  in
                             let uu____11219 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___309_11218.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___309_11218.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____11219;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___309_11218.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___309_11218.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11248  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___310_11273 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps =
                                 (uu___310_11273.FStar_TypeChecker_Cfg.steps);
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___310_11273.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___310_11273.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 (uu___310_11273.FStar_TypeChecker_Cfg.delta_level);
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___310_11273.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong = true;
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___310_11273.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___310_11273.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___310_11273.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           FStar_TypeChecker_Cfg.log cfg1
                             (fun uu____11276  ->
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
               let uu____11293 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____11293 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____11329 =
                               let uu___311_11330 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___311_11330.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___311_11330.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____11329  in
                           let uu____11331 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____11331 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____11357 =
                                   FStar_List.map (fun uu____11373  -> dummy)
                                     lbs1
                                    in
                                 let uu____11374 =
                                   let uu____11383 =
                                     FStar_List.map
                                       (fun uu____11405  -> dummy) xs1
                                      in
                                   FStar_List.append uu____11383 env  in
                                 FStar_List.append uu____11357 uu____11374
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____11431 =
                                       let uu___312_11432 = rc  in
                                       let uu____11433 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___312_11432.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____11433;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___312_11432.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____11431
                                 | uu____11442 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___313_11448 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___313_11448.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___313_11448.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___313_11448.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___313_11448.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____11458 =
                        FStar_List.map (fun uu____11474  -> dummy) lbs2  in
                      FStar_List.append uu____11458 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____11482 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____11482 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___314_11498 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___314_11498.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___314_11498.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
               ->
               let uu____11527 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____11527
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____11546 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____11622  ->
                        match uu____11622 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___315_11743 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___315_11743.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___315_11743.FStar_Syntax_Syntax.sort)
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
               (match uu____11546 with
                | (rec_env,memos,uu____11970) ->
                    let uu____12023 =
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
                             let uu____12334 =
                               let uu____12341 =
                                 let uu____12342 =
                                   let uu____12373 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____12373, false)
                                    in
                                 Clos uu____12342  in
                               (FStar_Pervasives_Native.None, uu____12341)
                                in
                             uu____12334 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____12477  ->
                     let uu____12478 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____12478);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____12500 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____12502::uu____12503 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____12508) ->
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
                             | uu____12535 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____12551 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____12551
                              | uu____12564 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____12570 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____12594 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____12608 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____12621 =
                        let uu____12622 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____12623 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____12622 uu____12623
                         in
                      failwith uu____12621
                    else
                      (let uu____12625 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____12625)
                | uu____12626 -> norm cfg env stack t2))

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
              let uu____12635 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____12635 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____12649  ->
                        let uu____12650 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____12650);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____12661  ->
                        let uu____12662 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____12663 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____12662 uu____12663);
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
                      | (UnivArgs (us',uu____12676))::stack1 ->
                          ((let uu____12685 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____12685
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____12689 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____12689) us'
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
                      | uu____12722 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____12725 ->
                          let uu____12728 =
                            let uu____12729 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____12729
                             in
                          failwith uu____12728
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
                  let uu___316_12753 = cfg  in
                  let uu____12754 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____12754;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___316_12753.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___316_12753.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___316_12753.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___316_12753.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___316_12753.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___316_12753.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___316_12753.FStar_TypeChecker_Cfg.reifying)
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
                let head0 = head1  in
                let head2 = FStar_Syntax_Util.unascribe head1  in
                FStar_TypeChecker_Cfg.log cfg
                  (fun uu____12789  ->
                     let uu____12790 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____12791 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____12790
                       uu____12791);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____12793 =
                   let uu____12794 = FStar_Syntax_Subst.compress head3  in
                   uu____12794.FStar_Syntax_Syntax.n  in
                 match uu____12793 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____12812 =
                         FStar_TypeChecker_Env.norm_eff_name
                           cfg.FStar_TypeChecker_Cfg.tcenv m
                          in
                       FStar_TypeChecker_Env.get_effect_decl
                         cfg.FStar_TypeChecker_Cfg.tcenv uu____12812
                        in
                     let uu____12813 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____12813 with
                      | (uu____12814,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____12824 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____12834 =
                                   let uu____12835 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____12835.FStar_Syntax_Syntax.n  in
                                 match uu____12834 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____12841,uu____12842))
                                     ->
                                     let uu____12851 =
                                       let uu____12852 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____12852.FStar_Syntax_Syntax.n  in
                                     (match uu____12851 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____12858,msrc,uu____12860))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____12869 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____12869
                                      | uu____12870 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____12871 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____12872 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____12872 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___317_12877 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___317_12877.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___317_12877.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___317_12877.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___317_12877.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___317_12877.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____12878 = FStar_List.tl stack  in
                                    let uu____12879 =
                                      let uu____12880 =
                                        let uu____12887 =
                                          let uu____12888 =
                                            let uu____12901 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____12901)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____12888
                                           in
                                        FStar_Syntax_Syntax.mk uu____12887
                                         in
                                      uu____12880
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____12878 uu____12879
                                | FStar_Pervasives_Native.None  ->
                                    let uu____12917 =
                                      let uu____12918 = is_return body  in
                                      match uu____12918 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____12922;
                                            FStar_Syntax_Syntax.vars =
                                              uu____12923;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____12926 -> false  in
                                    if uu____12917
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
                                           FStar_Syntax_Syntax.residual_typ =
                                             (FStar_Pervasives_Native.Some t);
                                           FStar_Syntax_Syntax.residual_flags
                                             = []
                                         }  in
                                       let body2 =
                                         let uu____12947 =
                                           let uu____12954 =
                                             let uu____12955 =
                                               let uu____12974 =
                                                 let uu____12983 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____12983]  in
                                               (uu____12974, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____12955
                                              in
                                           FStar_Syntax_Syntax.mk uu____12954
                                            in
                                         uu____12947
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____13025 =
                                           let uu____13026 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____13026.FStar_Syntax_Syntax.n
                                            in
                                         match uu____13025 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____13032::uu____13033::[])
                                             ->
                                             let uu____13038 =
                                               let uu____13045 =
                                                 let uu____13046 =
                                                   let uu____13053 =
                                                     let uu____13054 =
                                                       let uu____13055 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.FStar_TypeChecker_Cfg.tcenv
                                                         uu____13055
                                                        in
                                                     let uu____13056 =
                                                       let uu____13059 =
                                                         let uu____13060 =
                                                           close1 t  in
                                                         (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.FStar_TypeChecker_Cfg.tcenv
                                                           uu____13060
                                                          in
                                                       [uu____13059]  in
                                                     uu____13054 ::
                                                       uu____13056
                                                      in
                                                   (bind1, uu____13053)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____13046
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____13045
                                                in
                                             uu____13038
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____13066 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____13080 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____13080
                                         then
                                           let uu____13091 =
                                             let uu____13100 =
                                               FStar_TypeChecker_Cfg.embed_simple
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____13100
                                              in
                                           let uu____13101 =
                                             let uu____13112 =
                                               let uu____13121 =
                                                 FStar_TypeChecker_Cfg.embed_simple
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____13121
                                                in
                                             [uu____13112]  in
                                           uu____13091 :: uu____13101
                                         else []  in
                                       let reified =
                                         let uu____13158 =
                                           let uu____13165 =
                                             let uu____13166 =
                                               let uu____13183 =
                                                 let uu____13194 =
                                                   let uu____13205 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____13214 =
                                                     let uu____13225 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____13225]  in
                                                   uu____13205 :: uu____13214
                                                    in
                                                 let uu____13258 =
                                                   let uu____13269 =
                                                     let uu____13280 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____13289 =
                                                       let uu____13300 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____13309 =
                                                         let uu____13320 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____13329 =
                                                           let uu____13340 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____13340]  in
                                                         uu____13320 ::
                                                           uu____13329
                                                          in
                                                       uu____13300 ::
                                                         uu____13309
                                                        in
                                                     uu____13280 ::
                                                       uu____13289
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____13269
                                                    in
                                                 FStar_List.append
                                                   uu____13194 uu____13258
                                                  in
                                               (bind_inst, uu____13183)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____13166
                                              in
                                           FStar_Syntax_Syntax.mk uu____13165
                                            in
                                         uu____13158
                                           FStar_Pervasives_Native.None rng
                                          in
                                       FStar_TypeChecker_Cfg.log cfg
                                         (fun uu____13424  ->
                                            let uu____13425 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____13426 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____13425 uu____13426);
                                       (let uu____13427 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____13427 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let maybe_unfold_action head4 =
                       let maybe_extract_fv t1 =
                         let t2 =
                           let uu____13481 =
                             let uu____13482 = FStar_Syntax_Subst.compress t1
                                in
                             uu____13482.FStar_Syntax_Syntax.n  in
                           match uu____13481 with
                           | FStar_Syntax_Syntax.Tm_uinst (t2,uu____13486) ->
                               t2
                           | uu____13491 -> head4  in
                         let uu____13492 =
                           let uu____13493 = FStar_Syntax_Subst.compress t2
                              in
                           uu____13493.FStar_Syntax_Syntax.n  in
                         match uu____13492 with
                         | FStar_Syntax_Syntax.Tm_fvar x ->
                             FStar_Pervasives_Native.Some x
                         | uu____13499 -> FStar_Pervasives_Native.None  in
                       let uu____13500 = maybe_extract_fv head4  in
                       match uu____13500 with
                       | FStar_Pervasives_Native.Some x when
                           let uu____13510 = FStar_Syntax_Syntax.lid_of_fv x
                              in
                           FStar_TypeChecker_Env.is_action
                             cfg.FStar_TypeChecker_Cfg.tcenv uu____13510
                           ->
                           let head5 = norm cfg env [] head4  in
                           let action_unfolded =
                             let uu____13515 = maybe_extract_fv head5  in
                             match uu____13515 with
                             | FStar_Pervasives_Native.Some uu____13520 ->
                                 FStar_Pervasives_Native.Some true
                             | uu____13521 ->
                                 FStar_Pervasives_Native.Some false
                              in
                           (head5, action_unfolded)
                       | uu____13526 -> (head4, FStar_Pervasives_Native.None)
                        in
                     ((let uu____13532 = FStar_Options.defensive ()  in
                       if uu____13532
                       then
                         let is_arg_impure uu____13544 =
                           match uu____13544 with
                           | (e,q) ->
                               let uu____13557 =
                                 let uu____13558 =
                                   FStar_Syntax_Subst.compress e  in
                                 uu____13558.FStar_Syntax_Syntax.n  in
                               (match uu____13557 with
                                | FStar_Syntax_Syntax.Tm_meta
                                    (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                     (m1,m2,t'))
                                    ->
                                    let uu____13573 =
                                      FStar_Syntax_Util.is_pure_effect m1  in
                                    Prims.op_Negation uu____13573
                                | uu____13574 -> false)
                            in
                         let uu____13575 =
                           let uu____13576 =
                             let uu____13587 =
                               FStar_Syntax_Syntax.as_arg head_app  in
                             uu____13587 :: args  in
                           FStar_Util.for_some is_arg_impure uu____13576  in
                         (if uu____13575
                          then
                            let uu____13612 =
                              let uu____13617 =
                                let uu____13618 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____13618
                                 in
                              (FStar_Errors.Warning_Defensive, uu____13617)
                               in
                            FStar_Errors.log_issue
                              head3.FStar_Syntax_Syntax.pos uu____13612
                          else ())
                       else ());
                      (let uu____13621 = maybe_unfold_action head_app  in
                       match uu____13621 with
                       | (head_app1,found_action) ->
                           let mk1 tm =
                             FStar_Syntax_Syntax.mk tm
                               FStar_Pervasives_Native.None
                               head3.FStar_Syntax_Syntax.pos
                              in
                           let body =
                             mk1
                               (FStar_Syntax_Syntax.Tm_app (head_app1, args))
                              in
                           let body1 =
                             match found_action with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Syntax_Util.mk_reify body
                             | FStar_Pervasives_Native.Some (false ) ->
                                 mk1
                                   (FStar_Syntax_Syntax.Tm_meta
                                      (body,
                                        (FStar_Syntax_Syntax.Meta_monadic
                                           (m, t))))
                             | FStar_Pervasives_Native.Some (true ) -> body
                              in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____13666  ->
                                 let uu____13667 =
                                   FStar_Syntax_Print.term_to_string head0
                                    in
                                 let uu____13668 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                   uu____13667 uu____13668);
                            (let uu____13669 = FStar_List.tl stack  in
                             norm cfg env uu____13669 body1))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____13671) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____13695 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____13695  in
                     (FStar_TypeChecker_Cfg.log cfg
                        (fun uu____13699  ->
                           let uu____13700 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____13700);
                      (let uu____13701 = FStar_List.tl stack  in
                       norm cfg env uu____13701 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____13822  ->
                               match uu____13822 with
                               | (pat,wopt,tm) ->
                                   let uu____13870 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____13870)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____13902 = FStar_List.tl stack  in
                     norm cfg env uu____13902 tm
                 | uu____13903 -> fallback ())

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
              (fun uu____13917  ->
                 let uu____13918 = FStar_Ident.string_of_lid msrc  in
                 let uu____13919 = FStar_Ident.string_of_lid mtgt  in
                 let uu____13920 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____13918
                   uu____13919 uu____13920);
            (let uu____13921 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____13921
             then
               let ed =
                 let uu____13923 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____13923  in
               let uu____13924 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____13924 with
               | (uu____13925,return_repr) ->
                   let return_inst =
                     let uu____13938 =
                       let uu____13939 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____13939.FStar_Syntax_Syntax.n  in
                     match uu____13938 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____13945::[]) ->
                         let uu____13950 =
                           let uu____13957 =
                             let uu____13958 =
                               let uu____13965 =
                                 let uu____13966 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____13966]  in
                               (return_tm, uu____13965)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____13958  in
                           FStar_Syntax_Syntax.mk uu____13957  in
                         uu____13950 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____13972 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____13975 =
                     let uu____13982 =
                       let uu____13983 =
                         let uu____14000 =
                           let uu____14011 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____14020 =
                             let uu____14031 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____14031]  in
                           uu____14011 :: uu____14020  in
                         (return_inst, uu____14000)  in
                       FStar_Syntax_Syntax.Tm_app uu____13983  in
                     FStar_Syntax_Syntax.mk uu____13982  in
                   uu____13975 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____14080 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____14080 with
                | FStar_Pervasives_Native.None  ->
                    let uu____14083 =
                      let uu____14084 = FStar_Ident.text_of_lid msrc  in
                      let uu____14085 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____14084 uu____14085
                       in
                    failwith uu____14083
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14086;
                      FStar_TypeChecker_Env.mtarget = uu____14087;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14088;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____14110 =
                      let uu____14111 = FStar_Ident.text_of_lid msrc  in
                      let uu____14112 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____14111 uu____14112
                       in
                    failwith uu____14110
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14113;
                      FStar_TypeChecker_Env.mtarget = uu____14114;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14115;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____14150 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____14151 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____14150 t FStar_Syntax_Syntax.tun uu____14151))

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
                (fun uu____14221  ->
                   match uu____14221 with
                   | (a,imp) ->
                       let uu____14240 = norm cfg env [] a  in
                       (uu____14240, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____14250  ->
             let uu____14251 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____14252 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____14251 uu____14252);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____14276 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____14276
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___318_14279 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___318_14279.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___318_14279.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____14301 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____14301
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___319_14304 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___319_14304.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___319_14304.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____14349  ->
                      match uu____14349 with
                      | (a,i) ->
                          let uu____14368 = norm cfg env [] a  in
                          (uu____14368, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___263_14390  ->
                       match uu___263_14390 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____14394 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____14394
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___320_14402 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___321_14405 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___321_14405.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___320_14402.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___320_14402.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun uu____14408  ->
        match uu____14408 with
        | (x,imp) ->
            let uu____14415 =
              let uu___322_14416 = x  in
              let uu____14417 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___322_14416.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___322_14416.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____14417
              }  in
            (uu____14415, imp)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____14425 =
          FStar_List.fold_left
            (fun uu____14459  ->
               fun b  ->
                 match uu____14459 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____14425 with | (nbs,uu____14539) -> FStar_List.rev nbs

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
            let uu____14571 =
              let uu___323_14572 = rc  in
              let uu____14573 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___323_14572.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____14573;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___323_14572.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____14571
        | uu____14582 -> lopt

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
            (let uu____14591 = FStar_Syntax_Print.term_to_string tm  in
             let uu____14592 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____14591 uu____14592)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___264_14596  ->
      match uu___264_14596 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____14609 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____14609 with
           | FStar_Pervasives_Native.Some (t,uu____14617) -> t
           | FStar_Pervasives_Native.None  ->
               let uu____14626 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____14626)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____14634 = norm_cb cfg  in
            reduce_primops uu____14634 cfg env tm  in
          let uu____14641 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____14641
          then tm1
          else
            (let w t =
               let uu___324_14655 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___324_14655.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___324_14655.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____14666 =
                 let uu____14667 = FStar_Syntax_Util.unmeta t  in
                 uu____14667.FStar_Syntax_Syntax.n  in
               match uu____14666 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____14674 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____14735)::args1,(bv,uu____14738)::bs1) ->
                   let uu____14792 =
                     let uu____14793 = FStar_Syntax_Subst.compress t  in
                     uu____14793.FStar_Syntax_Syntax.n  in
                   (match uu____14792 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____14797 -> false)
               | ([],[]) -> true
               | (uu____14826,uu____14827) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____14876 = FStar_Syntax_Print.term_to_string t  in
                  let uu____14877 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____14876
                    uu____14877)
               else ();
               (let uu____14879 = FStar_Syntax_Util.head_and_args' t  in
                match uu____14879 with
                | (hd1,args) ->
                    let uu____14918 =
                      let uu____14919 = FStar_Syntax_Subst.compress hd1  in
                      uu____14919.FStar_Syntax_Syntax.n  in
                    (match uu____14918 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____14926 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____14927 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____14928 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____14926 uu____14927 uu____14928)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____14930 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____14947 = FStar_Syntax_Print.term_to_string t  in
                  let uu____14948 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____14947
                    uu____14948)
               else ();
               (let uu____14950 = FStar_Syntax_Util.is_squash t  in
                match uu____14950 with
                | FStar_Pervasives_Native.Some (uu____14961,t') ->
                    is_applied bs t'
                | uu____14973 ->
                    let uu____14982 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____14982 with
                     | FStar_Pervasives_Native.Some (uu____14993,t') ->
                         is_applied bs t'
                     | uu____15005 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____15029 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____15029 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____15036)::(q,uu____15038)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____15080 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____15081 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____15080 uu____15081)
                    else ();
                    (let uu____15083 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____15083 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____15088 =
                           let uu____15089 = FStar_Syntax_Subst.compress p
                              in
                           uu____15089.FStar_Syntax_Syntax.n  in
                         (match uu____15088 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____15097 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____15097))
                          | uu____15100 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____15103)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____15128 =
                           let uu____15129 = FStar_Syntax_Subst.compress p1
                              in
                           uu____15129.FStar_Syntax_Syntax.n  in
                         (match uu____15128 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____15137 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____15137))
                          | uu____15140 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____15144 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____15144 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____15149 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____15149 with
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
                                     let uu____15160 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____15160))
                               | uu____15163 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____15168)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____15193 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____15193 with
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
                                     let uu____15204 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____15204))
                               | uu____15207 -> FStar_Pervasives_Native.None)
                          | uu____15210 -> FStar_Pervasives_Native.None)
                     | uu____15213 -> FStar_Pervasives_Native.None))
               | uu____15216 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____15229 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____15229 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____15235)::[],uu____15236,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____15255 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____15256 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____15255
                         uu____15256)
                    else ();
                    is_quantified_const bv phi')
               | uu____15258 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____15271 =
                 let uu____15272 = FStar_Syntax_Subst.compress phi  in
                 uu____15272.FStar_Syntax_Syntax.n  in
               match uu____15271 with
               | FStar_Syntax_Syntax.Tm_match (uu____15277,br::brs) ->
                   let uu____15344 = br  in
                   (match uu____15344 with
                    | (uu____15361,uu____15362,e) ->
                        let r =
                          let uu____15383 = simp_t e  in
                          match uu____15383 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____15389 =
                                FStar_List.for_all
                                  (fun uu____15407  ->
                                     match uu____15407 with
                                     | (uu____15420,uu____15421,e') ->
                                         let uu____15435 = simp_t e'  in
                                         uu____15435 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____15389
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____15443 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____15452 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____15452
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____15487 =
                 match uu____15487 with
                 | (t1,q) ->
                     let uu____15508 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____15508 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____15540 -> (t1, q))
                  in
               let uu____15553 = FStar_Syntax_Util.head_and_args t  in
               match uu____15553 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____15631 =
                 let uu____15632 = FStar_Syntax_Util.unmeta ty  in
                 uu____15632.FStar_Syntax_Syntax.n  in
               match uu____15631 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____15636) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____15641,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____15665 -> false  in
             let simplify1 arg =
               let uu____15696 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____15696, arg)  in
             let uu____15709 = is_forall_const tm1  in
             match uu____15709 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____15714 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____15715 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____15714
                       uu____15715)
                  else ();
                  (let uu____15717 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____15717))
             | FStar_Pervasives_Native.None  ->
                 let uu____15718 =
                   let uu____15719 = FStar_Syntax_Subst.compress tm1  in
                   uu____15719.FStar_Syntax_Syntax.n  in
                 (match uu____15718 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____15723;
                              FStar_Syntax_Syntax.vars = uu____15724;_},uu____15725);
                         FStar_Syntax_Syntax.pos = uu____15726;
                         FStar_Syntax_Syntax.vars = uu____15727;_},args)
                      ->
                      let uu____15757 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____15757
                      then
                        let uu____15758 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____15758 with
                         | (FStar_Pervasives_Native.Some (true ),uu____15813)::
                             (uu____15814,(arg,uu____15816))::[] ->
                             maybe_auto_squash arg
                         | (uu____15881,(arg,uu____15883))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____15884)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____15949)::uu____15950::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____16013::(FStar_Pervasives_Native.Some (false
                                         ),uu____16014)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____16077 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____16093 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____16093
                         then
                           let uu____16094 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____16094 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____16149)::uu____16150::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____16213::(FStar_Pervasives_Native.Some (true
                                           ),uu____16214)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____16277)::(uu____16278,(arg,uu____16280))::[]
                               -> maybe_auto_squash arg
                           | (uu____16345,(arg,uu____16347))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____16348)::[]
                               -> maybe_auto_squash arg
                           | uu____16413 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____16429 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____16429
                            then
                              let uu____16430 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____16430 with
                              | uu____16485::(FStar_Pervasives_Native.Some
                                              (true ),uu____16486)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____16549)::uu____16550::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____16613)::(uu____16614,(arg,uu____16616))::[]
                                  -> maybe_auto_squash arg
                              | (uu____16681,(p,uu____16683))::(uu____16684,
                                                                (q,uu____16686))::[]
                                  ->
                                  let uu____16751 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____16751
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____16753 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____16769 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____16769
                               then
                                 let uu____16770 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____16770 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16825)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____16826)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____16891)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____16892)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16957)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____16958)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17023)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17024)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____17089,(arg,uu____17091))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____17092)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17157)::(uu____17158,(arg,uu____17160))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____17225,(arg,uu____17227))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____17228)::[]
                                     ->
                                     let uu____17293 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17293
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17294)::(uu____17295,(arg,uu____17297))::[]
                                     ->
                                     let uu____17362 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17362
                                 | (uu____17363,(p,uu____17365))::(uu____17366,
                                                                   (q,uu____17368))::[]
                                     ->
                                     let uu____17433 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____17433
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____17435 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____17451 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____17451
                                  then
                                    let uu____17452 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____17452 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____17507)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____17546)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____17585 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____17601 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____17601
                                     then
                                       match args with
                                       | (t,uu____17603)::[] ->
                                           let uu____17628 =
                                             let uu____17629 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17629.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17628 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17632::[],body,uu____17634)
                                                ->
                                                let uu____17669 = simp_t body
                                                   in
                                                (match uu____17669 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____17672 -> tm1)
                                            | uu____17675 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____17677))::(t,uu____17679)::[]
                                           ->
                                           let uu____17718 =
                                             let uu____17719 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17719.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17718 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17722::[],body,uu____17724)
                                                ->
                                                let uu____17759 = simp_t body
                                                   in
                                                (match uu____17759 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____17762 -> tm1)
                                            | uu____17765 -> tm1)
                                       | uu____17766 -> tm1
                                     else
                                       (let uu____17778 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____17778
                                        then
                                          match args with
                                          | (t,uu____17780)::[] ->
                                              let uu____17805 =
                                                let uu____17806 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17806.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17805 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17809::[],body,uu____17811)
                                                   ->
                                                   let uu____17846 =
                                                     simp_t body  in
                                                   (match uu____17846 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____17849 -> tm1)
                                               | uu____17852 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____17854))::(t,uu____17856)::[]
                                              ->
                                              let uu____17895 =
                                                let uu____17896 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17896.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17895 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17899::[],body,uu____17901)
                                                   ->
                                                   let uu____17936 =
                                                     simp_t body  in
                                                   (match uu____17936 with
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
                                                    | uu____17939 -> tm1)
                                               | uu____17942 -> tm1)
                                          | uu____17943 -> tm1
                                        else
                                          (let uu____17955 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____17955
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____17956;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____17957;_},uu____17958)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____17983;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____17984;_},uu____17985)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____18010 -> tm1
                                           else
                                             (let uu____18022 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____18022 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____18042 ->
                                                  let uu____18051 =
                                                    let uu____18058 =
                                                      norm_cb cfg  in
                                                    reduce_equality
                                                      uu____18058 cfg env
                                                     in
                                                  uu____18051 tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____18066;
                         FStar_Syntax_Syntax.vars = uu____18067;_},args)
                      ->
                      let uu____18093 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18093
                      then
                        let uu____18094 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18094 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18149)::
                             (uu____18150,(arg,uu____18152))::[] ->
                             maybe_auto_squash arg
                         | (uu____18217,(arg,uu____18219))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18220)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18285)::uu____18286::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18349::(FStar_Pervasives_Native.Some (false
                                         ),uu____18350)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18413 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18429 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18429
                         then
                           let uu____18430 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18430 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18485)::uu____18486::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18549::(FStar_Pervasives_Native.Some (true
                                           ),uu____18550)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18613)::(uu____18614,(arg,uu____18616))::[]
                               -> maybe_auto_squash arg
                           | (uu____18681,(arg,uu____18683))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18684)::[]
                               -> maybe_auto_squash arg
                           | uu____18749 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18765 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____18765
                            then
                              let uu____18766 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____18766 with
                              | uu____18821::(FStar_Pervasives_Native.Some
                                              (true ),uu____18822)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____18885)::uu____18886::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____18949)::(uu____18950,(arg,uu____18952))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19017,(p,uu____19019))::(uu____19020,
                                                                (q,uu____19022))::[]
                                  ->
                                  let uu____19087 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19087
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19089 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19105 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19105
                               then
                                 let uu____19106 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19106 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19161)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19162)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19227)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19228)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19293)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19294)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19359)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19360)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19425,(arg,uu____19427))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19428)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19493)::(uu____19494,(arg,uu____19496))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19561,(arg,uu____19563))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19564)::[]
                                     ->
                                     let uu____19629 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19629
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19630)::(uu____19631,(arg,uu____19633))::[]
                                     ->
                                     let uu____19698 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19698
                                 | (uu____19699,(p,uu____19701))::(uu____19702,
                                                                   (q,uu____19704))::[]
                                     ->
                                     let uu____19769 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19769
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19771 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19787 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19787
                                  then
                                    let uu____19788 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19788 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19843)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19882)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19921 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19937 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19937
                                     then
                                       match args with
                                       | (t,uu____19939)::[] ->
                                           let uu____19964 =
                                             let uu____19965 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19965.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19964 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19968::[],body,uu____19970)
                                                ->
                                                let uu____20005 = simp_t body
                                                   in
                                                (match uu____20005 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20008 -> tm1)
                                            | uu____20011 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20013))::(t,uu____20015)::[]
                                           ->
                                           let uu____20054 =
                                             let uu____20055 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20055.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20054 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20058::[],body,uu____20060)
                                                ->
                                                let uu____20095 = simp_t body
                                                   in
                                                (match uu____20095 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20098 -> tm1)
                                            | uu____20101 -> tm1)
                                       | uu____20102 -> tm1
                                     else
                                       (let uu____20114 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20114
                                        then
                                          match args with
                                          | (t,uu____20116)::[] ->
                                              let uu____20141 =
                                                let uu____20142 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20142.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20141 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20145::[],body,uu____20147)
                                                   ->
                                                   let uu____20182 =
                                                     simp_t body  in
                                                   (match uu____20182 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20185 -> tm1)
                                               | uu____20188 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20190))::(t,uu____20192)::[]
                                              ->
                                              let uu____20231 =
                                                let uu____20232 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20232.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20231 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20235::[],body,uu____20237)
                                                   ->
                                                   let uu____20272 =
                                                     simp_t body  in
                                                   (match uu____20272 with
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
                                                    | uu____20275 -> tm1)
                                               | uu____20278 -> tm1)
                                          | uu____20279 -> tm1
                                        else
                                          (let uu____20291 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20291
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20292;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20293;_},uu____20294)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20319;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20320;_},uu____20321)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20346 -> tm1
                                           else
                                             (let uu____20358 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20358 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20378 ->
                                                  let uu____20387 =
                                                    let uu____20394 =
                                                      norm_cb cfg  in
                                                    reduce_equality
                                                      uu____20394 cfg env
                                                     in
                                                  uu____20387 tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____20407 = simp_t t  in
                      (match uu____20407 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____20410 ->
                      let uu____20433 = is_const_match tm1  in
                      (match uu____20433 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____20436 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____20446  ->
               (let uu____20448 = FStar_Syntax_Print.tag_of_term t  in
                let uu____20449 = FStar_Syntax_Print.term_to_string t  in
                let uu____20450 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____20457 =
                  let uu____20458 =
                    let uu____20461 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____20461
                     in
                  stack_to_string uu____20458  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____20448 uu____20449 uu____20450 uu____20457);
               (let uu____20484 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____20484
                then
                  let uu____20485 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____20485 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____20492 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____20493 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____20494 =
                          let uu____20495 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____20495
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____20492
                          uu____20493 uu____20494);
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
                   let uu____20513 =
                     let uu____20514 =
                       let uu____20515 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____20515  in
                     FStar_Util.string_of_int uu____20514  in
                   let uu____20520 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____20521 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____20513 uu____20520 uu____20521)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____20527,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                FStar_TypeChecker_Cfg.log cfg
                  (fun uu____20578  ->
                     let uu____20579 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____20579);
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
               let uu____20617 =
                 let uu___325_20618 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___325_20618.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___325_20618.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____20617
           | (Arg (Univ uu____20621,uu____20622,uu____20623))::uu____20624 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____20627,uu____20628))::uu____20629 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____20644,uu____20645),aq,r))::stack1
               when
               let uu____20695 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____20695 ->
               let t2 =
                 let uu____20699 =
                   let uu____20704 =
                     let uu____20705 = closure_as_term cfg env_arg tm  in
                     (uu____20705, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____20704  in
                 uu____20699 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____20717),aq,r))::stack1 ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____20770  ->
                     let uu____20771 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____20771);
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
                  (let uu____20785 = FStar_ST.op_Bang m  in
                   match uu____20785 with
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
                   | FStar_Pervasives_Native.Some (uu____20926,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____20981 =
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____20985  ->
                      let uu____20986 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____20986);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____20994 =
                 let uu____20995 = FStar_Syntax_Subst.compress t1  in
                 uu____20995.FStar_Syntax_Syntax.n  in
               (match uu____20994 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____21022 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____21022  in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____21026  ->
                          let uu____21027 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____21027);
                     (let uu____21028 = FStar_List.tl stack  in
                      norm cfg env1 uu____21028 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____21029);
                       FStar_Syntax_Syntax.pos = uu____21030;
                       FStar_Syntax_Syntax.vars = uu____21031;_},(e,uu____21033)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____21072 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                    ->
                    let uu____21089 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____21089 with
                     | (hd1,args) ->
                         let uu____21132 =
                           let uu____21133 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____21133.FStar_Syntax_Syntax.n  in
                         (match uu____21132 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____21137 =
                                FStar_TypeChecker_Cfg.find_prim_step cfg fv
                                 in
                              (match uu____21137 with
                               | FStar_Pervasives_Native.Some
                                   {
                                     FStar_TypeChecker_Cfg.name = uu____21140;
                                     FStar_TypeChecker_Cfg.arity =
                                       uu____21141;
                                     FStar_TypeChecker_Cfg.univ_arity =
                                       uu____21142;
                                     FStar_TypeChecker_Cfg.auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     FStar_TypeChecker_Cfg.strong_reduction_ok
                                       = uu____21144;
                                     FStar_TypeChecker_Cfg.requires_binder_substitution
                                       = uu____21145;
                                     FStar_TypeChecker_Cfg.interpretation =
                                       uu____21146;
                                     FStar_TypeChecker_Cfg.interpretation_nbe
                                       = uu____21147;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____21181 -> fallback " (3)" ())
                          | uu____21184 -> fallback " (4)" ()))
                | uu____21185 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (FStar_TypeChecker_Cfg.log cfg1
                  (fun uu____21210  ->
                     let uu____21211 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____21211);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____21220 =
                   FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____21225  ->
                        let uu____21226 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____21227 =
                          let uu____21228 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____21255  ->
                                    match uu____21255 with
                                    | (p,uu____21265,uu____21266) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____21228
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____21226 uu____21227);
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
                             (fun uu___265_21283  ->
                                match uu___265_21283 with
                                | FStar_TypeChecker_Env.InliningDelta  ->
                                    true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____21284 -> false))
                         in
                      let steps =
                        let uu___326_21286 = cfg1.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___326_21286.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___326_21286.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta = false;
                          FStar_TypeChecker_Cfg.weak =
                            (uu___326_21286.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___326_21286.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___326_21286.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___326_21286.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___326_21286.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_tac = false;
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___326_21286.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___326_21286.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___326_21286.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___326_21286.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___326_21286.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___326_21286.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___326_21286.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___326_21286.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___326_21286.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___326_21286.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___326_21286.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___326_21286.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___326_21286.FStar_TypeChecker_Cfg.nbe_step)
                        }  in
                      let uu___327_21291 = cfg1  in
                      {
                        FStar_TypeChecker_Cfg.steps = steps;
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___327_21291.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___327_21291.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level = new_delta;
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___327_21291.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong = true;
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___327_21291.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___327_21291.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying =
                          (uu___327_21291.FStar_TypeChecker_Cfg.reifying)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____21363 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____21392 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____21476  ->
                                    fun uu____21477  ->
                                      match (uu____21476, uu____21477) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____21616 = norm_pat env3 p1
                                             in
                                          (match uu____21616 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____21392 with
                           | (pats1,env3) ->
                               ((let uu___328_21778 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___328_21778.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___329_21797 = x  in
                            let uu____21798 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___329_21797.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___329_21797.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21798
                            }  in
                          ((let uu___330_21812 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___330_21812.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___331_21823 = x  in
                            let uu____21824 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___331_21823.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___331_21823.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21824
                            }  in
                          ((let uu___332_21838 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___332_21838.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___333_21854 = x  in
                            let uu____21855 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___333_21854.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___333_21854.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21855
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___334_21870 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___334_21870.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____21914 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____21944 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____21944 with
                                  | (p,wopt,e) ->
                                      let uu____21964 = norm_pat env1 p  in
                                      (match uu____21964 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____22019 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____22019
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____22036 =
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
                      if uu____22036
                      then
                        norm
                          (let uu___335_22041 = cfg1  in
                           {
                             FStar_TypeChecker_Cfg.steps =
                               (let uu___336_22044 =
                                  cfg1.FStar_TypeChecker_Cfg.steps  in
                                {
                                  FStar_TypeChecker_Cfg.beta =
                                    (uu___336_22044.FStar_TypeChecker_Cfg.beta);
                                  FStar_TypeChecker_Cfg.iota =
                                    (uu___336_22044.FStar_TypeChecker_Cfg.iota);
                                  FStar_TypeChecker_Cfg.zeta =
                                    (uu___336_22044.FStar_TypeChecker_Cfg.zeta);
                                  FStar_TypeChecker_Cfg.weak =
                                    (uu___336_22044.FStar_TypeChecker_Cfg.weak);
                                  FStar_TypeChecker_Cfg.hnf =
                                    (uu___336_22044.FStar_TypeChecker_Cfg.hnf);
                                  FStar_TypeChecker_Cfg.primops =
                                    (uu___336_22044.FStar_TypeChecker_Cfg.primops);
                                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                    =
                                    (uu___336_22044.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                  FStar_TypeChecker_Cfg.unfold_until =
                                    (uu___336_22044.FStar_TypeChecker_Cfg.unfold_until);
                                  FStar_TypeChecker_Cfg.unfold_only =
                                    (uu___336_22044.FStar_TypeChecker_Cfg.unfold_only);
                                  FStar_TypeChecker_Cfg.unfold_fully =
                                    (uu___336_22044.FStar_TypeChecker_Cfg.unfold_fully);
                                  FStar_TypeChecker_Cfg.unfold_attr =
                                    (uu___336_22044.FStar_TypeChecker_Cfg.unfold_attr);
                                  FStar_TypeChecker_Cfg.unfold_tac =
                                    (uu___336_22044.FStar_TypeChecker_Cfg.unfold_tac);
                                  FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                    =
                                    (uu___336_22044.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                  FStar_TypeChecker_Cfg.simplify =
                                    (uu___336_22044.FStar_TypeChecker_Cfg.simplify);
                                  FStar_TypeChecker_Cfg.erase_universes =
                                    (uu___336_22044.FStar_TypeChecker_Cfg.erase_universes);
                                  FStar_TypeChecker_Cfg.allow_unbound_universes
                                    =
                                    (uu___336_22044.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                  FStar_TypeChecker_Cfg.reify_ =
                                    (uu___336_22044.FStar_TypeChecker_Cfg.reify_);
                                  FStar_TypeChecker_Cfg.compress_uvars =
                                    (uu___336_22044.FStar_TypeChecker_Cfg.compress_uvars);
                                  FStar_TypeChecker_Cfg.no_full_norm =
                                    (uu___336_22044.FStar_TypeChecker_Cfg.no_full_norm);
                                  FStar_TypeChecker_Cfg.check_no_uvars =
                                    (uu___336_22044.FStar_TypeChecker_Cfg.check_no_uvars);
                                  FStar_TypeChecker_Cfg.unmeta =
                                    (uu___336_22044.FStar_TypeChecker_Cfg.unmeta);
                                  FStar_TypeChecker_Cfg.unascribe =
                                    (uu___336_22044.FStar_TypeChecker_Cfg.unascribe);
                                  FStar_TypeChecker_Cfg.in_full_norm_request
                                    =
                                    (uu___336_22044.FStar_TypeChecker_Cfg.in_full_norm_request);
                                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                    = false;
                                  FStar_TypeChecker_Cfg.nbe_step =
                                    (uu___336_22044.FStar_TypeChecker_Cfg.nbe_step)
                                });
                             FStar_TypeChecker_Cfg.tcenv =
                               (uu___335_22041.FStar_TypeChecker_Cfg.tcenv);
                             FStar_TypeChecker_Cfg.debug =
                               (uu___335_22041.FStar_TypeChecker_Cfg.debug);
                             FStar_TypeChecker_Cfg.delta_level =
                               (uu___335_22041.FStar_TypeChecker_Cfg.delta_level);
                             FStar_TypeChecker_Cfg.primitive_steps =
                               (uu___335_22041.FStar_TypeChecker_Cfg.primitive_steps);
                             FStar_TypeChecker_Cfg.strong =
                               (uu___335_22041.FStar_TypeChecker_Cfg.strong);
                             FStar_TypeChecker_Cfg.memoize_lazy =
                               (uu___335_22041.FStar_TypeChecker_Cfg.memoize_lazy);
                             FStar_TypeChecker_Cfg.normalize_pure_lets =
                               (uu___335_22041.FStar_TypeChecker_Cfg.normalize_pure_lets);
                             FStar_TypeChecker_Cfg.reifying =
                               (uu___335_22041.FStar_TypeChecker_Cfg.reifying)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____22046 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____22046)
                    in
                 let rec is_cons head1 =
                   let uu____22071 =
                     let uu____22072 = FStar_Syntax_Subst.compress head1  in
                     uu____22072.FStar_Syntax_Syntax.n  in
                   match uu____22071 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____22076) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____22081 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____22082;
                         FStar_Syntax_Syntax.fv_delta = uu____22083;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____22084;
                         FStar_Syntax_Syntax.fv_delta = uu____22085;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____22086);_}
                       -> true
                   | uu____22093 -> false  in
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
                   let uu____22257 =
                     FStar_Syntax_Util.head_and_args scrutinee2  in
                   match uu____22257 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____22350 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee2.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____22389 ->
                                 let uu____22390 =
                                   let uu____22391 = is_cons head1  in
                                   Prims.op_Negation uu____22391  in
                                 FStar_Util.Inr uu____22390)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____22416 =
                              let uu____22417 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____22417.FStar_Syntax_Syntax.n  in
                            (match uu____22416 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____22435 ->
                                 let uu____22436 =
                                   let uu____22437 = is_cons head1  in
                                   Prims.op_Negation uu____22437  in
                                 FStar_Util.Inr uu____22436))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____22520)::rest_a,(p1,uu____22523)::rest_p) ->
                       let uu____22577 = matches_pat t2 p1  in
                       (match uu____22577 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____22626 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____22746 = matches_pat scrutinee1 p1  in
                       (match uu____22746 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (FStar_TypeChecker_Cfg.log cfg1
                               (fun uu____22786  ->
                                  let uu____22787 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____22788 =
                                    let uu____22789 =
                                      FStar_List.map
                                        (fun uu____22799  ->
                                           match uu____22799 with
                                           | (uu____22804,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____22789
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____22787 uu____22788);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____22836  ->
                                       match uu____22836 with
                                       | (bv,t2) ->
                                           let uu____22859 =
                                             let uu____22866 =
                                               let uu____22869 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____22869
                                                in
                                             let uu____22870 =
                                               let uu____22871 =
                                                 let uu____22902 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____22902, false)
                                                  in
                                               Clos uu____22871  in
                                             (uu____22866, uu____22870)  in
                                           uu____22859 :: env2) env1 s
                                 in
                              let uu____23015 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____23015)))
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
            (fun uu____23045  ->
               let uu____23046 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____23046);
          (let uu____23047 = is_nbe_request s  in
           if uu____23047
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____23051  ->
                   let uu____23052 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____23052);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____23056  ->
                   let uu____23057 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____23057);
              (let r = nbe_eval c s t  in
               FStar_TypeChecker_Cfg.log_top c
                 (fun uu____23062  ->
                    let uu____23063 = FStar_Syntax_Print.term_to_string r  in
                    FStar_Util.print1 "}\nNormalization result = (%s)\n"
                      uu____23063);
               r))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____23068  ->
                   let uu____23069 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____23069);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____23073  ->
                   let uu____23074 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____23074);
              (let r = norm c [] [] t  in
               FStar_TypeChecker_Cfg.log_top c
                 (fun uu____23085  ->
                    let uu____23086 = FStar_Syntax_Print.term_to_string r  in
                    FStar_Util.print1 "}\nNormalization result = (%s)\n"
                      uu____23086);
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
        let uu____23117 = FStar_TypeChecker_Cfg.config s e  in
        norm_comp uu____23117 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____23134 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____23134 [] u
  
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
        let uu____23158 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____23158  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____23165 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___337_23184 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___337_23184.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___337_23184.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name
              cfg.FStar_TypeChecker_Cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____23191 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____23191
          then
            let ct1 =
              let uu____23193 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____23193 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____23200 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____23200
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___338_23204 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___338_23204.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___338_23204.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___338_23204.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev
                      cfg.FStar_TypeChecker_Cfg.tcenv c
                     in
                  let uu___339_23206 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___339_23206.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___339_23206.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___339_23206.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___339_23206.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___340_23207 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___340_23207.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___340_23207.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____23209 -> c
  
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
        let uu____23227 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____23227  in
      let uu____23234 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____23234
      then
        let uu____23235 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____23235 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____23241  ->
                 let uu____23242 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____23242)
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
          (fun uu___342_23256  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___341_23259 ->
            ((let uu____23261 =
                let uu____23266 =
                  let uu____23267 = FStar_Util.message_of_exn uu___341_23259
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23267
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____23266)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____23261);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          (fun uu___344_23281  ->
             match () with
             | () ->
                 let uu____23282 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____23282 [] c) ()
        with
        | uu___343_23291 ->
            ((let uu____23293 =
                let uu____23298 =
                  let uu____23299 = FStar_Util.message_of_exn uu___343_23291
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23299
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____23298)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____23293);
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
                   let uu____23344 =
                     let uu____23345 =
                       let uu____23352 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____23352)  in
                     FStar_Syntax_Syntax.Tm_refine uu____23345  in
                   mk uu____23344 t01.FStar_Syntax_Syntax.pos
               | uu____23357 -> t2)
          | uu____23358 -> t2  in
        aux t
  
let (unfold_whnf' :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t  ->
        normalize
          (FStar_List.append steps
             [FStar_TypeChecker_Env.Primops;
             FStar_TypeChecker_Env.Weak;
             FStar_TypeChecker_Env.HNF;
             FStar_TypeChecker_Env.UnfoldUntil
               FStar_Syntax_Syntax.delta_constant;
             FStar_TypeChecker_Env.Beta]) env t
  
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
        let uu____23437 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____23437 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____23474 ->
                 let uu____23483 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____23483 with
                  | (actuals,uu____23493,uu____23494) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____23512 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____23512 with
                         | (binders,args) ->
                             let uu____23523 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____23523
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
      | uu____23537 ->
          let uu____23538 = FStar_Syntax_Util.head_and_args t  in
          (match uu____23538 with
           | (head1,args) ->
               let uu____23581 =
                 let uu____23582 = FStar_Syntax_Subst.compress head1  in
                 uu____23582.FStar_Syntax_Syntax.n  in
               (match uu____23581 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____23603 =
                      let uu____23618 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____23618  in
                    (match uu____23603 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____23656 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___345_23664 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___345_23664.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___345_23664.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___345_23664.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___345_23664.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___345_23664.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___345_23664.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___345_23664.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___345_23664.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___345_23664.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___345_23664.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___345_23664.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___345_23664.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___345_23664.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___345_23664.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___345_23664.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___345_23664.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___345_23664.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___345_23664.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___345_23664.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___345_23664.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___345_23664.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___345_23664.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___345_23664.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___345_23664.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___345_23664.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___345_23664.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___345_23664.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___345_23664.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___345_23664.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___345_23664.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___345_23664.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___345_23664.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___345_23664.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___345_23664.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___345_23664.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___345_23664.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___345_23664.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___345_23664.FStar_TypeChecker_Env.dep_graph);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___345_23664.FStar_TypeChecker_Env.nbe)
                                 }) t
                               in
                            match uu____23656 with
                            | (uu____23665,ty,uu____23667) ->
                                eta_expand_with_type env t ty))
                | uu____23668 ->
                    let uu____23669 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___346_23677 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___346_23677.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___346_23677.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___346_23677.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___346_23677.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___346_23677.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___346_23677.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___346_23677.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___346_23677.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___346_23677.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___346_23677.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___346_23677.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___346_23677.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___346_23677.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___346_23677.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___346_23677.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___346_23677.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___346_23677.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___346_23677.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___346_23677.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___346_23677.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___346_23677.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___346_23677.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___346_23677.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___346_23677.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___346_23677.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___346_23677.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___346_23677.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___346_23677.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___346_23677.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___346_23677.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___346_23677.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___346_23677.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___346_23677.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___346_23677.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___346_23677.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___346_23677.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___346_23677.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___346_23677.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___346_23677.FStar_TypeChecker_Env.nbe)
                         }) t
                       in
                    (match uu____23669 with
                     | (uu____23678,ty,uu____23680) ->
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
      let uu___347_23761 = x  in
      let uu____23762 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___347_23761.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___347_23761.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____23762
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____23765 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____23788 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____23789 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____23790 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____23791 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____23798 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____23799 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____23800 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___348_23834 = rc  in
          let uu____23835 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____23844 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___348_23834.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____23835;
            FStar_Syntax_Syntax.residual_flags = uu____23844
          }  in
        let uu____23847 =
          let uu____23848 =
            let uu____23867 = elim_delayed_subst_binders bs  in
            let uu____23876 = elim_delayed_subst_term t2  in
            let uu____23879 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____23867, uu____23876, uu____23879)  in
          FStar_Syntax_Syntax.Tm_abs uu____23848  in
        mk1 uu____23847
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____23916 =
          let uu____23917 =
            let uu____23932 = elim_delayed_subst_binders bs  in
            let uu____23941 = elim_delayed_subst_comp c  in
            (uu____23932, uu____23941)  in
          FStar_Syntax_Syntax.Tm_arrow uu____23917  in
        mk1 uu____23916
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____23960 =
          let uu____23961 =
            let uu____23968 = elim_bv bv  in
            let uu____23969 = elim_delayed_subst_term phi  in
            (uu____23968, uu____23969)  in
          FStar_Syntax_Syntax.Tm_refine uu____23961  in
        mk1 uu____23960
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____24000 =
          let uu____24001 =
            let uu____24018 = elim_delayed_subst_term t2  in
            let uu____24021 = elim_delayed_subst_args args  in
            (uu____24018, uu____24021)  in
          FStar_Syntax_Syntax.Tm_app uu____24001  in
        mk1 uu____24000
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___349_24093 = p  in
              let uu____24094 =
                let uu____24095 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____24095  in
              {
                FStar_Syntax_Syntax.v = uu____24094;
                FStar_Syntax_Syntax.p =
                  (uu___349_24093.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___350_24097 = p  in
              let uu____24098 =
                let uu____24099 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____24099  in
              {
                FStar_Syntax_Syntax.v = uu____24098;
                FStar_Syntax_Syntax.p =
                  (uu___350_24097.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___351_24106 = p  in
              let uu____24107 =
                let uu____24108 =
                  let uu____24115 = elim_bv x  in
                  let uu____24116 = elim_delayed_subst_term t0  in
                  (uu____24115, uu____24116)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____24108  in
              {
                FStar_Syntax_Syntax.v = uu____24107;
                FStar_Syntax_Syntax.p =
                  (uu___351_24106.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___352_24139 = p  in
              let uu____24140 =
                let uu____24141 =
                  let uu____24154 =
                    FStar_List.map
                      (fun uu____24177  ->
                         match uu____24177 with
                         | (x,b) ->
                             let uu____24190 = elim_pat x  in
                             (uu____24190, b)) pats
                     in
                  (fv, uu____24154)  in
                FStar_Syntax_Syntax.Pat_cons uu____24141  in
              {
                FStar_Syntax_Syntax.v = uu____24140;
                FStar_Syntax_Syntax.p =
                  (uu___352_24139.FStar_Syntax_Syntax.p)
              }
          | uu____24203 -> p  in
        let elim_branch uu____24227 =
          match uu____24227 with
          | (pat,wopt,t3) ->
              let uu____24253 = elim_pat pat  in
              let uu____24256 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____24259 = elim_delayed_subst_term t3  in
              (uu____24253, uu____24256, uu____24259)
           in
        let uu____24264 =
          let uu____24265 =
            let uu____24288 = elim_delayed_subst_term t2  in
            let uu____24291 = FStar_List.map elim_branch branches  in
            (uu____24288, uu____24291)  in
          FStar_Syntax_Syntax.Tm_match uu____24265  in
        mk1 uu____24264
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____24422 =
          match uu____24422 with
          | (tc,topt) ->
              let uu____24457 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____24467 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____24467
                | FStar_Util.Inr c ->
                    let uu____24469 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____24469
                 in
              let uu____24470 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____24457, uu____24470)
           in
        let uu____24479 =
          let uu____24480 =
            let uu____24507 = elim_delayed_subst_term t2  in
            let uu____24510 = elim_ascription a  in
            (uu____24507, uu____24510, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____24480  in
        mk1 uu____24479
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___353_24571 = lb  in
          let uu____24572 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____24575 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___353_24571.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___353_24571.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____24572;
            FStar_Syntax_Syntax.lbeff =
              (uu___353_24571.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____24575;
            FStar_Syntax_Syntax.lbattrs =
              (uu___353_24571.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___353_24571.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____24578 =
          let uu____24579 =
            let uu____24592 =
              let uu____24599 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____24599)  in
            let uu____24608 = elim_delayed_subst_term t2  in
            (uu____24592, uu____24608)  in
          FStar_Syntax_Syntax.Tm_let uu____24579  in
        mk1 uu____24578
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____24652 =
          let uu____24653 =
            let uu____24660 = elim_delayed_subst_term tm  in
            (uu____24660, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____24653  in
        mk1 uu____24652
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____24671 =
          let uu____24672 =
            let uu____24679 = elim_delayed_subst_term t2  in
            let uu____24682 = elim_delayed_subst_meta md  in
            (uu____24679, uu____24682)  in
          FStar_Syntax_Syntax.Tm_meta uu____24672  in
        mk1 uu____24671

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___266_24691  ->
         match uu___266_24691 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____24695 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____24695
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
        let uu____24718 =
          let uu____24719 =
            let uu____24728 = elim_delayed_subst_term t  in
            (uu____24728, uopt)  in
          FStar_Syntax_Syntax.Total uu____24719  in
        mk1 uu____24718
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____24745 =
          let uu____24746 =
            let uu____24755 = elim_delayed_subst_term t  in
            (uu____24755, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____24746  in
        mk1 uu____24745
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___354_24764 = ct  in
          let uu____24765 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____24768 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____24779 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___354_24764.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___354_24764.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____24765;
            FStar_Syntax_Syntax.effect_args = uu____24768;
            FStar_Syntax_Syntax.flags = uu____24779
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___267_24782  ->
    match uu___267_24782 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____24796 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____24796
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____24835 =
          let uu____24842 = elim_delayed_subst_term t  in (m, uu____24842)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____24835
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____24854 =
          let uu____24863 = elim_delayed_subst_term t  in
          (m1, m2, uu____24863)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____24854
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
      (fun uu____24896  ->
         match uu____24896 with
         | (t,q) ->
             let uu____24915 = elim_delayed_subst_term t  in (uu____24915, q))
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
      (fun uu____24943  ->
         match uu____24943 with
         | (x,q) ->
             let uu____24962 =
               let uu___355_24963 = x  in
               let uu____24964 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___355_24963.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___355_24963.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____24964
               }  in
             (uu____24962, q)) bs

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
            | (uu____25070,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____25102,FStar_Util.Inl t) ->
                let uu____25124 =
                  let uu____25131 =
                    let uu____25132 =
                      let uu____25147 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____25147)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____25132  in
                  FStar_Syntax_Syntax.mk uu____25131  in
                uu____25124 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____25163 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____25163 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____25195 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____25268 ->
                    let uu____25269 =
                      let uu____25278 =
                        let uu____25279 = FStar_Syntax_Subst.compress t4  in
                        uu____25279.FStar_Syntax_Syntax.n  in
                      (uu____25278, tc)  in
                    (match uu____25269 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____25308) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____25355) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____25400,FStar_Util.Inl uu____25401) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____25432 -> failwith "Impossible")
                 in
              (match uu____25195 with
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
          let uu____25569 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____25569 with
          | (univ_names1,binders1,tc) ->
              let uu____25643 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____25643)
  
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
          let uu____25696 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____25696 with
          | (univ_names1,binders1,tc) ->
              let uu____25770 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____25770)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____25811 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____25811 with
           | (univ_names1,binders1,typ1) ->
               let uu___356_25851 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___356_25851.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___356_25851.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___356_25851.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___356_25851.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___357_25866 = s  in
          let uu____25867 =
            let uu____25868 =
              let uu____25877 = FStar_List.map (elim_uvars env) sigs  in
              (uu____25877, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____25868  in
          {
            FStar_Syntax_Syntax.sigel = uu____25867;
            FStar_Syntax_Syntax.sigrng =
              (uu___357_25866.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___357_25866.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___357_25866.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___357_25866.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____25894 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25894 with
           | (univ_names1,uu____25918,typ1) ->
               let uu___358_25940 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___358_25940.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___358_25940.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___358_25940.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___358_25940.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____25946 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25946 with
           | (univ_names1,uu____25970,typ1) ->
               let uu___359_25992 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___359_25992.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___359_25992.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___359_25992.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___359_25992.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____26020 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____26020 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____26045 =
                            let uu____26046 =
                              let uu____26047 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____26047  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____26046
                             in
                          elim_delayed_subst_term uu____26045  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___360_26050 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___360_26050.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___360_26050.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___360_26050.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___360_26050.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___361_26051 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___361_26051.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___361_26051.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___361_26051.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___361_26051.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___362_26057 = s  in
          let uu____26058 =
            let uu____26059 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____26059  in
          {
            FStar_Syntax_Syntax.sigel = uu____26058;
            FStar_Syntax_Syntax.sigrng =
              (uu___362_26057.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___362_26057.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___362_26057.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___362_26057.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____26063 = elim_uvars_aux_t env us [] t  in
          (match uu____26063 with
           | (us1,uu____26087,t1) ->
               let uu___363_26109 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___363_26109.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___363_26109.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___363_26109.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___363_26109.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____26110 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____26112 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____26112 with
           | (univs1,binders,signature) ->
               let uu____26152 =
                 let uu____26157 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____26157 with
                 | (univs_opening,univs2) ->
                     let uu____26180 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____26180)
                  in
               (match uu____26152 with
                | (univs_opening,univs_closing) ->
                    let uu____26183 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____26189 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____26190 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____26189, uu____26190)  in
                    (match uu____26183 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____26216 =
                           match uu____26216 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____26234 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____26234 with
                                | (us1,t1) ->
                                    let uu____26245 =
                                      let uu____26254 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____26265 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____26254, uu____26265)  in
                                    (match uu____26245 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____26294 =
                                           let uu____26303 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____26314 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____26303, uu____26314)  in
                                         (match uu____26294 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____26344 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____26344
                                                 in
                                              let uu____26345 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____26345 with
                                               | (uu____26372,uu____26373,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____26396 =
                                                       let uu____26397 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____26397
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____26396
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____26406 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____26406 with
                           | (uu____26425,uu____26426,t1) -> t1  in
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
                             | uu____26502 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____26529 =
                               let uu____26530 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____26530.FStar_Syntax_Syntax.n  in
                             match uu____26529 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____26589 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____26622 =
                               let uu____26623 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____26623.FStar_Syntax_Syntax.n  in
                             match uu____26622 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____26646) ->
                                 let uu____26671 = destruct_action_body body
                                    in
                                 (match uu____26671 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____26720 ->
                                 let uu____26721 = destruct_action_body t  in
                                 (match uu____26721 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____26776 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____26776 with
                           | (action_univs,t) ->
                               let uu____26785 = destruct_action_typ_templ t
                                  in
                               (match uu____26785 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___364_26832 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___364_26832.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___364_26832.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___365_26834 = ed  in
                           let uu____26835 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____26836 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____26837 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____26838 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____26839 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____26840 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____26841 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____26842 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____26843 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____26844 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____26845 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____26846 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____26847 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____26848 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___365_26834.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___365_26834.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____26835;
                             FStar_Syntax_Syntax.bind_wp = uu____26836;
                             FStar_Syntax_Syntax.if_then_else = uu____26837;
                             FStar_Syntax_Syntax.ite_wp = uu____26838;
                             FStar_Syntax_Syntax.stronger = uu____26839;
                             FStar_Syntax_Syntax.close_wp = uu____26840;
                             FStar_Syntax_Syntax.assert_p = uu____26841;
                             FStar_Syntax_Syntax.assume_p = uu____26842;
                             FStar_Syntax_Syntax.null_wp = uu____26843;
                             FStar_Syntax_Syntax.trivial = uu____26844;
                             FStar_Syntax_Syntax.repr = uu____26845;
                             FStar_Syntax_Syntax.return_repr = uu____26846;
                             FStar_Syntax_Syntax.bind_repr = uu____26847;
                             FStar_Syntax_Syntax.actions = uu____26848;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___365_26834.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___366_26851 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___366_26851.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___366_26851.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___366_26851.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___366_26851.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___268_26872 =
            match uu___268_26872 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____26903 = elim_uvars_aux_t env us [] t  in
                (match uu____26903 with
                 | (us1,uu____26935,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___367_26966 = sub_eff  in
            let uu____26967 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____26970 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___367_26966.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___367_26966.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____26967;
              FStar_Syntax_Syntax.lift = uu____26970
            }  in
          let uu___368_26973 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___368_26973.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___368_26973.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___368_26973.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___368_26973.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____26983 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____26983 with
           | (univ_names1,binders1,comp1) ->
               let uu___369_27023 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___369_27023.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___369_27023.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___369_27023.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___369_27023.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____27026 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____27027 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      normalize
        [FStar_TypeChecker_Env.EraseUniverses;
        FStar_TypeChecker_Env.AllowUnboundUniverses] env t
  