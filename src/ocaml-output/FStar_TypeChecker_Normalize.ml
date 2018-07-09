open Prims
let cases :
  'Auu____11 'Auu____12 .
    ('Auu____11 -> 'Auu____12) ->
      'Auu____12 -> 'Auu____11 FStar_Pervasives_Native.option -> 'Auu____12
  =
  fun f  ->
    fun d  ->
      fun uu___250_32  ->
        match uu___250_32 with
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
  fun uu___251_1097  ->
    match uu___251_1097 with
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
  fun uu___252_1159  ->
    match uu___252_1159 with
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
  fun uu___253_1249  ->
    match uu___253_1249 with | [] -> true | uu____1252 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        (fun uu___272_1283  ->
           match () with
           | () ->
               let uu____1284 =
                 FStar_List.nth env x.FStar_Syntax_Syntax.index  in
               FStar_Pervasives_Native.snd uu____1284) ()
      with
      | uu___271_1301 ->
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
                 (fun uu___274_1463  ->
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
                                      (fun uu___254_1859  ->
                                         match uu___254_1859 with
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
                                                 (let uu___275_1883 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___275_1883.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___275_1883.FStar_Syntax_Syntax.sort)
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
                         let uu___276_1895 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___276_1895.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___276_1895.FStar_Syntax_Syntax.vars)
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
                           let uu___277_1934 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___277_1934.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___277_1934.FStar_Syntax_Syntax.index);
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
                             (let uu___278_2734 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___278_2734.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___278_2734.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____2718))
                       in
                    (match uu____2688 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___279_2752 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___279_2752.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___279_2752.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___279_2752.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___279_2752.FStar_Syntax_Syntax.lbpos)
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
                             (let uu___280_2890 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___280_2890.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___280_2890.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___281_2891 = lb  in
                      let uu____2892 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___281_2891.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___281_2891.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____2892;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___281_2891.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___281_2891.FStar_Syntax_Syntax.lbpos)
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
                      let uu___282_3141 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___282_3141.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___282_3141.FStar_Syntax_Syntax.vars)
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
                                ((let uu___283_3727 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___283_3727.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___284_3746 = x  in
                             let uu____3747 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___284_3746.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___284_3746.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3747
                             }  in
                           ((let uu___285_3761 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___285_3761.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___286_3772 = x  in
                             let uu____3773 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___286_3772.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___286_3772.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3773
                             }  in
                           ((let uu___287_3787 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___287_3787.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___288_3803 = x  in
                             let uu____3804 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___288_3803.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___288_3803.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3804
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___289_3821 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___289_3821.FStar_Syntax_Syntax.p)
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
                          let uu___290_4481 = b  in
                          let uu____4482 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___290_4481.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___290_4481.FStar_Syntax_Syntax.index);
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
                        (fun uu___255_4739  ->
                           match uu___255_4739 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4743 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____4743
                           | f -> f))
                    in
                 let uu____4747 =
                   let uu___291_4748 = c1  in
                   let uu____4749 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4749;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___291_4748.FStar_Syntax_Syntax.effect_name);
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
         (fun uu___256_4759  ->
            match uu___256_4759 with
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
                   (fun uu___257_4781  ->
                      match uu___257_4781 with
                      | FStar_Syntax_Syntax.DECREASES uu____4782 -> false
                      | uu____4785 -> true))
               in
            let rc1 =
              let uu___292_4787 = rc  in
              let uu____4788 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___292_4787.FStar_Syntax_Syntax.residual_effect);
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
                                      let uu___293_5109 = bv  in
                                      let uu____5110 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___293_5109.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___293_5109.FStar_Syntax_Syntax.index);
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
                                      (fun uu___258_5139  ->
                                         match uu___258_5139 with
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
          (let uu___294_5660 = cfg  in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___295_5663 = FStar_TypeChecker_Cfg.default_steps  in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___295_5663.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___295_5663.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___295_5663.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___295_5663.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___295_5663.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___295_5663.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___295_5663.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___295_5663.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___295_5663.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___295_5663.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___295_5663.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___295_5663.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___295_5663.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___295_5663.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___295_5663.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___295_5663.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___295_5663.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___295_5663.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___295_5663.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___295_5663.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___295_5663.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___295_5663.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___295_5663.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___295_5663.FStar_TypeChecker_Cfg.nbe_step)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___294_5660.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___294_5660.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___294_5660.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___294_5660.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___294_5660.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___294_5660.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___294_5660.FStar_TypeChecker_Cfg.reifying)
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
  fun uu___259_5735  ->
    match uu___259_5735 with
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
                 (fun uu___260_6053  ->
                    match uu___260_6053 with
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
  fun uu___261_6098  ->
    match uu___261_6098 with
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
      let rec drop_irrel uu___262_6171 =
        match uu___262_6171 with
        | (MemoLazy uu____6176)::s -> drop_irrel s
        | s -> s  in
      let uu____6189 = drop_irrel stack  in
      match uu____6189 with
      | (App
          (uu____6192,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____6193;
                        FStar_Syntax_Syntax.vars = uu____6194;_},uu____6195,uu____6196))::uu____6197
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____6202 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____6225) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____6235) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____6256  ->
                  match uu____6256 with
                  | (a,uu____6266) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6276 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____6299 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____6300 -> false
    | FStar_Syntax_Syntax.Tm_type uu____6313 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____6314 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____6315 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____6316 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____6317 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____6318 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____6325 -> false
    | FStar_Syntax_Syntax.Tm_let uu____6332 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____6345 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____6364 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____6379 -> true
    | FStar_Syntax_Syntax.Tm_match uu____6386 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____6456  ->
                   match uu____6456 with
                   | (a,uu____6466) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____6477) ->
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
                     (fun uu____6605  ->
                        match uu____6605 with
                        | (a,uu____6615) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____6624,uu____6625,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____6631,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____6637 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____6644 -> false
            | FStar_Syntax_Syntax.Meta_named uu____6645 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____6651 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____6657 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_fully  -> true | uu____6663 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_reify  -> true | uu____6669 -> false
  
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
            let uu____6698 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
            match uu____6698 with
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
              (fun uu____6826  ->
                 fun uu____6827  ->
                   match (uu____6826, uu____6827) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____6887 =
            match uu____6887 with
            | (x,y,z) ->
                let uu____6897 = FStar_Util.string_of_bool x  in
                let uu____6898 = FStar_Util.string_of_bool y  in
                let uu____6899 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____6897 uu____6898
                  uu____6899
             in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg  in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____6918  ->
                    let uu____6919 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____6920 = FStar_Util.string_of_bool b  in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____6919 uu____6920);
               if b then reif else no)
            else
              if
                (let uu____6928 = FStar_TypeChecker_Cfg.find_prim_step cfg fv
                    in
                 FStar_Option.isSome uu____6928)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____6933  ->
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
                          ((is_rec,uu____6967),uu____6968);
                        FStar_Syntax_Syntax.sigrng = uu____6969;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____6971;
                        FStar_Syntax_Syntax.sigattrs = uu____6972;_},uu____6973),uu____6974),uu____6975,uu____6976,uu____6977)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7082  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____7083,uu____7084,uu____7085,uu____7086) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7153  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____7155),uu____7156);
                        FStar_Syntax_Syntax.sigrng = uu____7157;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7159;
                        FStar_Syntax_Syntax.sigattrs = uu____7160;_},uu____7161),uu____7162),uu____7163,uu____7164,uu____7165)
                     when
                     is_rec &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7270  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____7271,FStar_Pervasives_Native.Some
                    uu____7272,uu____7273,uu____7274) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7342  ->
                           let uu____7343 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____7343);
                      (let uu____7344 =
                         let uu____7353 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____7373 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____7373
                            in
                         let uu____7380 =
                           let uu____7389 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____7409 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____7409
                              in
                           let uu____7418 =
                             let uu____7427 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____7447 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____7447
                                in
                             [uu____7427]  in
                           uu____7389 :: uu____7418  in
                         uu____7353 :: uu____7380  in
                       comb_or uu____7344))
                 | (uu____7478,uu____7479,FStar_Pervasives_Native.Some
                    uu____7480,uu____7481) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7549  ->
                           let uu____7550 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____7550);
                      (let uu____7551 =
                         let uu____7560 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____7580 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____7580
                            in
                         let uu____7587 =
                           let uu____7596 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____7616 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____7616
                              in
                           let uu____7625 =
                             let uu____7634 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____7654 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____7654
                                in
                             [uu____7634]  in
                           uu____7596 :: uu____7625  in
                         uu____7560 :: uu____7587  in
                       comb_or uu____7551))
                 | (uu____7685,uu____7686,uu____7687,FStar_Pervasives_Native.Some
                    uu____7688) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7756  ->
                           let uu____7757 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____7757);
                      (let uu____7758 =
                         let uu____7767 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____7787 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____7787
                            in
                         let uu____7794 =
                           let uu____7803 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some ats ->
                                 let uu____7823 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (FStar_Syntax_Util.attr_eq at) ats)
                                     attrs
                                    in
                                 FStar_All.pipe_left yesno uu____7823
                              in
                           let uu____7832 =
                             let uu____7841 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____7861 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____7861
                                in
                             [uu____7841]  in
                           uu____7803 :: uu____7832  in
                         uu____7767 :: uu____7794  in
                       comb_or uu____7758))
                 | uu____7892 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7938  ->
                           let uu____7939 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____7940 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____7941 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level
                              in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____7939 uu____7940 uu____7941);
                      (let uu____7942 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___263_7946  ->
                                 match uu___263_7946 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.InliningDelta  ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       fv.FStar_Syntax_Syntax.fv_delta l))
                          in
                       FStar_All.pipe_left yesno uu____7942)))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____7959  ->
               let uu____7960 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____7961 =
                 let uu____7962 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____7962  in
               let uu____7963 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____7960 uu____7961 uu____7963);
          (match res with
           | (false ,uu____7964,uu____7965) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____7966 ->
               let uu____7973 =
                 let uu____7974 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____7974
                  in
               FStar_All.pipe_left failwith uu____7973)
  
let decide_unfolding :
  'Auu____7989 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'Auu____7989 ->
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
                    let uu___296_8058 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___297_8061 = cfg.FStar_TypeChecker_Cfg.steps
                            in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___297_8061.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___297_8061.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___297_8061.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___297_8061.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___297_8061.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___297_8061.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___297_8061.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___297_8061.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___297_8061.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___297_8061.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___297_8061.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___297_8061.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___297_8061.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___297_8061.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___297_8061.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___297_8061.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___297_8061.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___297_8061.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___297_8061.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___297_8061.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___297_8061.FStar_TypeChecker_Cfg.nbe_step)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___296_8058.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___296_8058.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___296_8058.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___296_8058.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___296_8058.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___296_8058.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___296_8058.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___296_8058.FStar_TypeChecker_Cfg.reifying)
                    }  in
                  let stack' =
                    match stack with
                    | (UnivArgs i)::stack' -> (UnivArgs i) :: (Cfg cfg) ::
                        stack'
                    | stack' -> (Cfg cfg) :: stack'  in
                  FStar_Pervasives_Native.Some (cfg', stack')
              | Should_unfold_reify  ->
                  let ref =
                    let uu____8097 =
                      let uu____8104 =
                        let uu____8105 =
                          let uu____8106 = FStar_Syntax_Syntax.lid_of_fv fv
                             in
                          FStar_Const.Const_reflect uu____8106  in
                        FStar_Syntax_Syntax.Tm_constant uu____8105  in
                      FStar_Syntax_Syntax.mk uu____8104  in
                    uu____8097 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  FStar_Pervasives_Native.Some
                    (cfg,
                      ((App
                          (env, ref, FStar_Pervasives_Native.None,
                            FStar_Range.dummyRange)) :: stack))
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____8394 ->
                   let uu____8417 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____8417
               | uu____8418 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____8427  ->
               let uu____8428 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____8429 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____8430 = FStar_Syntax_Print.term_to_string t1  in
               let uu____8431 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____8438 =
                 let uu____8439 =
                   let uu____8442 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8442
                    in
                 stack_to_string uu____8439  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____8428 uu____8429 uu____8430 uu____8431 uu____8438);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____8468  ->
               let uu____8469 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____8469);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8473  ->
                     let uu____8474 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8474);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____8475 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8479  ->
                     let uu____8480 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8480);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____8481 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8485  ->
                     let uu____8486 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8486);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____8487 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8491  ->
                     let uu____8492 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8492);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8493;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_17;
                 FStar_Syntax_Syntax.fv_qual = uu____8494;_}
               when _0_17 = (Prims.parse_int "0") ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8500  ->
                     let uu____8501 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8501);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8502;
                 FStar_Syntax_Syntax.fv_delta = uu____8503;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8507  ->
                     let uu____8508 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8508);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8509;
                 FStar_Syntax_Syntax.fv_delta = uu____8510;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____8511);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8521  ->
                     let uu____8522 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8522);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____8525 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv uu____8525
                  in
               let uu____8526 =
                 decide_unfolding cfg env stack t1.FStar_Syntax_Syntax.pos fv
                   qninfo
                  in
               (match uu____8526 with
                | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                    do_unfold_fv cfg1 env stack1 t1 qninfo fv
                | FStar_Pervasives_Native.None  -> rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_quoted uu____8553 ->
               let uu____8560 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____8560
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
                  && (is_norm_request hd1 args))
                 &&
                 (let uu____8596 =
                    FStar_Ident.lid_equals
                      (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____8596)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___298_8600 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___299_8603 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___299_8603.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___299_8603.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___299_8603.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___299_8603.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___299_8603.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___299_8603.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___299_8603.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___299_8603.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___299_8603.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___299_8603.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___299_8603.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___299_8603.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___299_8603.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___299_8603.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___299_8603.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___299_8603.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___299_8603.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___299_8603.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___299_8603.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___299_8603.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___299_8603.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___299_8603.FStar_TypeChecker_Cfg.nbe_step)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___298_8600.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___298_8600.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___298_8600.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___298_8600.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___298_8600.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___298_8600.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____8608 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____8608 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____8641  ->
                                 fun stack1  ->
                                   match uu____8641 with
                                   | (a,aq) ->
                                       let uu____8653 =
                                         let uu____8654 =
                                           let uu____8661 =
                                             let uu____8662 =
                                               let uu____8693 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____8693, false)
                                                in
                                             Clos uu____8662  in
                                           (uu____8661, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____8654  in
                                       uu____8653 :: stack1) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____8781  ->
                            let uu____8782 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____8782);
                       norm cfg env stack1 hd1))
                 | FStar_Pervasives_Native.Some (s,tm) when is_nbe_request s
                     ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____8804 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting NBE request on %s ... \n" uu____8804)
                      else ();
                      (let tm' = closure_as_term cfg env tm  in
                       let start = FStar_Util.now ()  in
                       let tm_norm = nbe_eval cfg s tm'  in
                       let fin = FStar_Util.now ()  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         (let uu____8811 =
                            let uu____8812 =
                              let uu____8813 = FStar_Util.time_diff start fin
                                 in
                              FStar_Pervasives_Native.snd uu____8813  in
                            FStar_Util.string_of_int uu____8812  in
                          let uu____8818 =
                            FStar_Syntax_Print.term_to_string tm'  in
                          let uu____8819 =
                            FStar_Syntax_Print.term_to_string tm_norm  in
                          FStar_Util.print3 "NBE'd (%s ms) %s\n\tto %s\n"
                            uu____8811 uu____8818 uu____8819)
                       else ();
                       norm cfg env stack tm_norm))
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____8834 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting norm request on %s ... \n" uu____8834)
                      else ();
                      (let delta_level =
                         let uu____8839 =
                           FStar_All.pipe_right s
                             (FStar_Util.for_some
                                (fun uu___264_8844  ->
                                   match uu___264_8844 with
                                   | FStar_TypeChecker_Env.UnfoldUntil
                                       uu____8845 -> true
                                   | FStar_TypeChecker_Env.UnfoldOnly
                                       uu____8846 -> true
                                   | FStar_TypeChecker_Env.UnfoldFully
                                       uu____8849 -> true
                                   | uu____8852 -> false))
                            in
                         if uu____8839
                         then
                           [FStar_TypeChecker_Env.Unfold
                              FStar_Syntax_Syntax.delta_constant]
                         else [FStar_TypeChecker_Env.NoDelta]  in
                       let cfg'1 =
                         let uu___300_8857 = cfg  in
                         let uu____8858 =
                           let uu___301_8859 =
                             FStar_TypeChecker_Cfg.to_fsteps s  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___301_8859.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___301_8859.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___301_8859.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak =
                               (uu___301_8859.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___301_8859.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___301_8859.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___301_8859.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___301_8859.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               (uu___301_8859.FStar_TypeChecker_Cfg.unfold_only);
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___301_8859.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___301_8859.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___301_8859.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___301_8859.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___301_8859.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___301_8859.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___301_8859.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___301_8859.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___301_8859.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___301_8859.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___301_8859.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___301_8859.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___301_8859.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               true;
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___301_8859.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___301_8859.FStar_TypeChecker_Cfg.nbe_step)
                           }  in
                         {
                           FStar_TypeChecker_Cfg.steps = uu____8858;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___300_8857.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___300_8857.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = delta_level;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___300_8857.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong =
                             (uu___300_8857.FStar_TypeChecker_Cfg.strong);
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___300_8857.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___300_8857.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let stack' =
                         let tail1 = (Cfg cfg) :: stack  in
                         if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           let uu____8864 =
                             let uu____8865 =
                               let uu____8870 = FStar_Util.now ()  in
                               (t1, uu____8870)  in
                             Debug uu____8865  in
                           uu____8864 :: tail1
                         else tail1  in
                       norm cfg'1 env stack' tm))))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____8874 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____8874
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____8883 =
                      let uu____8890 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____8890, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____8883  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____8899 = lookup_bvar env x  in
               (match uu____8899 with
                | Univ uu____8900 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                    then
                      let uu____8949 = FStar_ST.op_Bang r  in
                      (match uu____8949 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9067  ->
                                 let uu____9068 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____9069 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____9068
                                   uu____9069);
                            (let uu____9070 = maybe_weakly_reduced t'  in
                             if uu____9070
                             then
                               match stack with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____9071 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____9146)::uu____9147 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____9157,uu____9158))::stack_rest ->
                    (match c with
                     | Univ uu____9162 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____9171 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____9200  ->
                                    let uu____9201 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____9201);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____9235  ->
                                    let uu____9236 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____9236);
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
                       (fun uu____9304  ->
                          let uu____9305 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____9305);
                     norm cfg env stack1 t1)
                | (Match uu____9306)::uu____9307 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9320 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9320 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9356  -> dummy :: env1) env)
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
                                          let uu____9399 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9399)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___302_9406 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___302_9406.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___302_9406.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9407 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9413  ->
                                 let uu____9414 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9414);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___303_9425 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___303_9425.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___303_9425.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___303_9425.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___303_9425.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___303_9425.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___303_9425.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___303_9425.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___303_9425.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____9428)::uu____9429 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9438 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9438 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9474  -> dummy :: env1) env)
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
                                          let uu____9517 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9517)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___302_9524 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___302_9524.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___302_9524.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9525 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9531  ->
                                 let uu____9532 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9532);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___303_9543 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___303_9543.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___303_9543.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___303_9543.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___303_9543.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___303_9543.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___303_9543.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___303_9543.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___303_9543.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____9546)::uu____9547 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9558 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9558 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9594  -> dummy :: env1) env)
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
                                          let uu____9637 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9637)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___302_9644 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___302_9644.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___302_9644.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9645 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9651  ->
                                 let uu____9652 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9652);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___303_9663 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___303_9663.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___303_9663.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___303_9663.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___303_9663.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___303_9663.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___303_9663.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___303_9663.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___303_9663.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____9666)::uu____9667 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9680 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9680 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9716  -> dummy :: env1) env)
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
                                          let uu____9759 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9759)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___302_9766 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___302_9766.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___302_9766.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9767 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9773  ->
                                 let uu____9774 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9774);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___303_9785 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___303_9785.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___303_9785.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___303_9785.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___303_9785.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___303_9785.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___303_9785.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___303_9785.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___303_9785.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____9788)::uu____9789 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9802 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9802 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9838  -> dummy :: env1) env)
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
                                          let uu____9881 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9881)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___302_9888 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___302_9888.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___302_9888.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9889 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9895  ->
                                 let uu____9896 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9896);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___303_9907 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___303_9907.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___303_9907.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___303_9907.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___303_9907.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___303_9907.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___303_9907.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___303_9907.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___303_9907.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____9910)::uu____9911 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9928 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9928 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9964  -> dummy :: env1) env)
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
                                          let uu____10007 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10007)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___302_10014 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___302_10014.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___302_10014.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10015 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10021  ->
                                 let uu____10022 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10022);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___303_10033 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___303_10033.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___303_10033.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___303_10033.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___303_10033.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___303_10033.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___303_10033.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___303_10033.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___303_10033.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____10038 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10038 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10074  -> dummy :: env1) env)
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
                                          let uu____10117 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10117)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___302_10124 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___302_10124.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___302_10124.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10125 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10131  ->
                                 let uu____10132 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10132);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___303_10143 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___303_10143.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___303_10143.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___303_10143.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___303_10143.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___303_10143.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___303_10143.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___303_10143.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___303_10143.FStar_TypeChecker_Cfg.reifying)
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
                      (fun uu____10186  ->
                         fun stack1  ->
                           match uu____10186 with
                           | (a,aq) ->
                               let uu____10198 =
                                 let uu____10199 =
                                   let uu____10206 =
                                     let uu____10207 =
                                       let uu____10238 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____10238, false)  in
                                     Clos uu____10207  in
                                   (uu____10206, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____10199  in
                               uu____10198 :: stack1) args)
                  in
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____10326  ->
                     let uu____10327 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____10327);
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
                             ((let uu___304_10375 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___304_10375.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___304_10375.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____10376 ->
                      let uu____10391 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10391)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____10394 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____10394 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____10425 =
                          let uu____10426 =
                            let uu____10433 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___305_10439 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___305_10439.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___305_10439.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____10433)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____10426  in
                        mk uu____10425 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____10462 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____10462
               else
                 (let uu____10464 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____10464 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____10472 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____10498  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____10472 c1  in
                      let t2 =
                        let uu____10522 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____10522 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____10635)::uu____10636 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10649  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____10650)::uu____10651 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10662  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____10663,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____10664;
                                   FStar_Syntax_Syntax.vars = uu____10665;_},uu____10666,uu____10667))::uu____10668
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10675  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____10676)::uu____10677 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10688  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____10689 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10692  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____10696  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____10721 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____10721
                         | FStar_Util.Inr c ->
                             let uu____10735 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____10735
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____10758 =
                               let uu____10759 =
                                 let uu____10786 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____10786, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____10759
                                in
                             mk uu____10758 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____10821 ->
                           let uu____10822 =
                             let uu____10823 =
                               let uu____10824 =
                                 let uu____10851 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____10851, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____10824
                                in
                             mk uu____10823 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____10822))))
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
                   let uu___306_10928 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___307_10931 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___307_10931.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___307_10931.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___307_10931.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___307_10931.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___307_10931.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___307_10931.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___307_10931.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___307_10931.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___307_10931.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___307_10931.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___307_10931.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___307_10931.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___307_10931.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___307_10931.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___307_10931.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___307_10931.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___307_10931.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___307_10931.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___307_10931.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___307_10931.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___307_10931.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___307_10931.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___307_10931.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___307_10931.FStar_TypeChecker_Cfg.nbe_step)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___306_10928.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___306_10928.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___306_10928.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___306_10928.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___306_10928.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___306_10928.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___306_10928.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___306_10928.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____10967 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____10967 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___308_10987 = cfg  in
                               let uu____10988 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___308_10987.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____10988;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___308_10987.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___308_10987.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___308_10987.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___308_10987.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___308_10987.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___308_10987.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___308_10987.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____10995 =
                                 let uu____10996 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____10996  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____10995
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___309_10999 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___309_10999.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___309_10999.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___309_10999.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___309_10999.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____11000 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____11000
           | FStar_Syntax_Syntax.Tm_let
               ((uu____11011,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____11012;
                               FStar_Syntax_Syntax.lbunivs = uu____11013;
                               FStar_Syntax_Syntax.lbtyp = uu____11014;
                               FStar_Syntax_Syntax.lbeff = uu____11015;
                               FStar_Syntax_Syntax.lbdef = uu____11016;
                               FStar_Syntax_Syntax.lbattrs = uu____11017;
                               FStar_Syntax_Syntax.lbpos = uu____11018;_}::uu____11019),uu____11020)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name
                   cfg.FStar_TypeChecker_Cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____11060 =
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
               if uu____11060
               then
                 let binder =
                   let uu____11062 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____11062  in
                 let env1 =
                   let uu____11072 =
                     let uu____11079 =
                       let uu____11080 =
                         let uu____11111 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____11111,
                           false)
                          in
                       Clos uu____11080  in
                     ((FStar_Pervasives_Native.Some binder), uu____11079)  in
                   uu____11072 :: env  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____11206  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                 then
                   (FStar_TypeChecker_Cfg.log cfg
                      (fun uu____11210  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____11211 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____11211))
                 else
                   (let uu____11213 =
                      let uu____11218 =
                        let uu____11219 =
                          let uu____11226 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____11226
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____11219]  in
                      FStar_Syntax_Subst.open_term uu____11218 body  in
                    match uu____11213 with
                    | (bs,body1) ->
                        (FStar_TypeChecker_Cfg.log cfg
                           (fun uu____11253  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____11261 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____11261  in
                            FStar_Util.Inl
                              (let uu___310_11277 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___310_11277.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___310_11277.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____11280  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___311_11282 = lb  in
                             let uu____11283 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___311_11282.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___311_11282.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____11283;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___311_11282.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___311_11282.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11312  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___312_11337 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps =
                                 (uu___312_11337.FStar_TypeChecker_Cfg.steps);
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___312_11337.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___312_11337.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 (uu___312_11337.FStar_TypeChecker_Cfg.delta_level);
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___312_11337.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong = true;
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___312_11337.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___312_11337.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___312_11337.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           FStar_TypeChecker_Cfg.log cfg1
                             (fun uu____11340  ->
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
               let uu____11357 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____11357 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____11393 =
                               let uu___313_11394 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___313_11394.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___313_11394.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____11393  in
                           let uu____11395 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____11395 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____11421 =
                                   FStar_List.map (fun uu____11437  -> dummy)
                                     lbs1
                                    in
                                 let uu____11438 =
                                   let uu____11447 =
                                     FStar_List.map
                                       (fun uu____11469  -> dummy) xs1
                                      in
                                   FStar_List.append uu____11447 env  in
                                 FStar_List.append uu____11421 uu____11438
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____11495 =
                                       let uu___314_11496 = rc  in
                                       let uu____11497 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___314_11496.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____11497;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___314_11496.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____11495
                                 | uu____11506 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___315_11512 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___315_11512.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___315_11512.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___315_11512.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___315_11512.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____11522 =
                        FStar_List.map (fun uu____11538  -> dummy) lbs2  in
                      FStar_List.append uu____11522 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____11546 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____11546 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___316_11562 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___316_11562.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___316_11562.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
               ->
               let uu____11591 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____11591
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____11610 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____11686  ->
                        match uu____11686 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___317_11807 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___317_11807.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___317_11807.FStar_Syntax_Syntax.sort)
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
               (match uu____11610 with
                | (rec_env,memos,uu____12034) ->
                    let uu____12087 =
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
                             let uu____12398 =
                               let uu____12405 =
                                 let uu____12406 =
                                   let uu____12437 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____12437, false)
                                    in
                                 Clos uu____12406  in
                               (FStar_Pervasives_Native.None, uu____12405)
                                in
                             uu____12398 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____12541  ->
                     let uu____12542 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____12542);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____12564 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____12566::uu____12567 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____12572) ->
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
                             | uu____12599 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____12615 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____12615
                              | uu____12628 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____12634 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____12658 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____12672 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____12685 =
                        let uu____12686 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____12687 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____12686 uu____12687
                         in
                      failwith uu____12685
                    else
                      (let uu____12689 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____12689)
                | uu____12690 -> norm cfg env stack t2))

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
              let uu____12699 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____12699 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____12713  ->
                        let uu____12714 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____12714);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____12725  ->
                        let uu____12726 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____12727 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____12726 uu____12727);
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
                      | (UnivArgs (us',uu____12740))::stack1 ->
                          ((let uu____12749 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____12749
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____12753 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____12753) us'
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
                      | uu____12786 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____12789 ->
                          let uu____12792 =
                            let uu____12793 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____12793
                             in
                          failwith uu____12792
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
                  let uu___318_12817 = cfg  in
                  let uu____12818 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____12818;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___318_12817.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___318_12817.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___318_12817.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___318_12817.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___318_12817.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___318_12817.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___318_12817.FStar_TypeChecker_Cfg.reifying)
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
                  (fun uu____12853  ->
                     let uu____12854 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____12855 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____12854
                       uu____12855);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____12857 =
                   let uu____12858 = FStar_Syntax_Subst.compress head3  in
                   uu____12858.FStar_Syntax_Syntax.n  in
                 match uu____12857 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____12876 =
                         FStar_TypeChecker_Env.norm_eff_name
                           cfg.FStar_TypeChecker_Cfg.tcenv m
                          in
                       FStar_TypeChecker_Env.get_effect_decl
                         cfg.FStar_TypeChecker_Cfg.tcenv uu____12876
                        in
                     let uu____12877 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____12877 with
                      | (uu____12878,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____12888 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____12898 =
                                   let uu____12899 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____12899.FStar_Syntax_Syntax.n  in
                                 match uu____12898 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____12905,uu____12906))
                                     ->
                                     let uu____12915 =
                                       let uu____12916 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____12916.FStar_Syntax_Syntax.n  in
                                     (match uu____12915 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____12922,msrc,uu____12924))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____12933 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____12933
                                      | uu____12934 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____12935 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____12936 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____12936 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___319_12941 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___319_12941.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___319_12941.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___319_12941.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___319_12941.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___319_12941.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____12942 = FStar_List.tl stack  in
                                    let uu____12943 =
                                      let uu____12944 =
                                        let uu____12951 =
                                          let uu____12952 =
                                            let uu____12965 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____12965)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____12952
                                           in
                                        FStar_Syntax_Syntax.mk uu____12951
                                         in
                                      uu____12944
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____12942 uu____12943
                                | FStar_Pervasives_Native.None  ->
                                    let uu____12981 =
                                      let uu____12982 = is_return body  in
                                      match uu____12982 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____12986;
                                            FStar_Syntax_Syntax.vars =
                                              uu____12987;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____12990 -> false  in
                                    if uu____12981
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
                                         let uu____13011 =
                                           let uu____13018 =
                                             let uu____13019 =
                                               let uu____13038 =
                                                 let uu____13047 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____13047]  in
                                               (uu____13038, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____13019
                                              in
                                           FStar_Syntax_Syntax.mk uu____13018
                                            in
                                         uu____13011
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____13089 =
                                           let uu____13090 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____13090.FStar_Syntax_Syntax.n
                                            in
                                         match uu____13089 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____13096::uu____13097::[])
                                             ->
                                             let uu____13102 =
                                               let uu____13109 =
                                                 let uu____13110 =
                                                   let uu____13117 =
                                                     let uu____13118 =
                                                       let uu____13119 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.FStar_TypeChecker_Cfg.tcenv
                                                         uu____13119
                                                        in
                                                     let uu____13120 =
                                                       let uu____13123 =
                                                         let uu____13124 =
                                                           close1 t  in
                                                         (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.FStar_TypeChecker_Cfg.tcenv
                                                           uu____13124
                                                          in
                                                       [uu____13123]  in
                                                     uu____13118 ::
                                                       uu____13120
                                                      in
                                                   (bind1, uu____13117)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____13110
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____13109
                                                in
                                             uu____13102
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____13130 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____13144 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____13144
                                         then
                                           let uu____13155 =
                                             let uu____13164 =
                                               FStar_TypeChecker_Cfg.embed_simple
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____13164
                                              in
                                           let uu____13165 =
                                             let uu____13176 =
                                               let uu____13185 =
                                                 FStar_TypeChecker_Cfg.embed_simple
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____13185
                                                in
                                             [uu____13176]  in
                                           uu____13155 :: uu____13165
                                         else []  in
                                       let reified =
                                         let uu____13222 =
                                           let uu____13229 =
                                             let uu____13230 =
                                               let uu____13247 =
                                                 let uu____13258 =
                                                   let uu____13269 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____13278 =
                                                     let uu____13289 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____13289]  in
                                                   uu____13269 :: uu____13278
                                                    in
                                                 let uu____13322 =
                                                   let uu____13333 =
                                                     let uu____13344 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____13353 =
                                                       let uu____13364 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____13373 =
                                                         let uu____13384 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____13393 =
                                                           let uu____13404 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____13404]  in
                                                         uu____13384 ::
                                                           uu____13393
                                                          in
                                                       uu____13364 ::
                                                         uu____13373
                                                        in
                                                     uu____13344 ::
                                                       uu____13353
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____13333
                                                    in
                                                 FStar_List.append
                                                   uu____13258 uu____13322
                                                  in
                                               (bind_inst, uu____13247)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____13230
                                              in
                                           FStar_Syntax_Syntax.mk uu____13229
                                            in
                                         uu____13222
                                           FStar_Pervasives_Native.None rng
                                          in
                                       FStar_TypeChecker_Cfg.log cfg
                                         (fun uu____13488  ->
                                            let uu____13489 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____13490 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____13489 uu____13490);
                                       (let uu____13491 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____13491 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     ((let uu____13519 = FStar_Options.defensive ()  in
                       if uu____13519
                       then
                         let is_arg_impure uu____13531 =
                           match uu____13531 with
                           | (e,q) ->
                               let uu____13544 =
                                 let uu____13545 =
                                   FStar_Syntax_Subst.compress e  in
                                 uu____13545.FStar_Syntax_Syntax.n  in
                               (match uu____13544 with
                                | FStar_Syntax_Syntax.Tm_meta
                                    (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                     (m1,m2,t'))
                                    ->
                                    let uu____13560 =
                                      FStar_Syntax_Util.is_pure_effect m1  in
                                    Prims.op_Negation uu____13560
                                | uu____13561 -> false)
                            in
                         let uu____13562 =
                           let uu____13563 =
                             let uu____13574 =
                               FStar_Syntax_Syntax.as_arg head_app  in
                             uu____13574 :: args  in
                           FStar_Util.for_some is_arg_impure uu____13563  in
                         (if uu____13562
                          then
                            let uu____13599 =
                              let uu____13604 =
                                let uu____13605 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____13605
                                 in
                              (FStar_Errors.Warning_Defensive, uu____13604)
                               in
                            FStar_Errors.log_issue
                              head3.FStar_Syntax_Syntax.pos uu____13599
                          else ())
                       else ());
                      (let fallback1 uu____13613 =
                         FStar_TypeChecker_Cfg.log cfg
                           (fun uu____13617  ->
                              let uu____13618 =
                                FStar_Syntax_Print.term_to_string head0  in
                              FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                uu____13618 "");
                         (let uu____13619 = FStar_List.tl stack  in
                          let uu____13620 = FStar_Syntax_Util.mk_reify head3
                             in
                          norm cfg env uu____13619 uu____13620)
                          in
                       let fallback2 uu____13626 =
                         FStar_TypeChecker_Cfg.log cfg
                           (fun uu____13630  ->
                              let uu____13631 =
                                FStar_Syntax_Print.term_to_string head0  in
                              FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                uu____13631 "");
                         (let uu____13632 = FStar_List.tl stack  in
                          let uu____13633 =
                            mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (head3,
                                   (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                              head0.FStar_Syntax_Syntax.pos
                             in
                          norm cfg env uu____13632 uu____13633)
                          in
                       let uu____13638 =
                         let uu____13639 =
                           FStar_Syntax_Util.un_uinst head_app  in
                         uu____13639.FStar_Syntax_Syntax.n  in
                       match uu____13638 with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                           let qninfo =
                             FStar_TypeChecker_Env.lookup_qname
                               cfg.FStar_TypeChecker_Cfg.tcenv lid
                              in
                           let uu____13645 =
                             let uu____13646 =
                               FStar_TypeChecker_Env.is_action
                                 cfg.FStar_TypeChecker_Cfg.tcenv lid
                                in
                             Prims.op_Negation uu____13646  in
                           if uu____13645
                           then fallback1 ()
                           else
                             (let uu____13648 =
                                let uu____13649 =
                                  FStar_TypeChecker_Env.lookup_definition_qninfo
                                    cfg.FStar_TypeChecker_Cfg.delta_level
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    qninfo
                                   in
                                FStar_Option.isNone uu____13649  in
                              if uu____13648
                              then fallback2 ()
                              else
                                (let t1 =
                                   let uu____13664 =
                                     let uu____13669 =
                                       FStar_Syntax_Util.mk_reify head_app
                                        in
                                     FStar_Syntax_Syntax.mk_Tm_app
                                       uu____13669 args
                                      in
                                   uu____13664 FStar_Pervasives_Native.None
                                     t.FStar_Syntax_Syntax.pos
                                    in
                                 let uu____13672 = FStar_List.tl stack  in
                                 norm cfg env uu____13672 t1))
                       | uu____13673 -> fallback1 ()))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____13675) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____13699 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____13699  in
                     (FStar_TypeChecker_Cfg.log cfg
                        (fun uu____13703  ->
                           let uu____13704 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____13704);
                      (let uu____13705 = FStar_List.tl stack  in
                       norm cfg env uu____13705 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____13826  ->
                               match uu____13826 with
                               | (pat,wopt,tm) ->
                                   let uu____13874 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____13874)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____13906 = FStar_List.tl stack  in
                     norm cfg env uu____13906 tm
                 | uu____13907 -> fallback ())

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
              (fun uu____13921  ->
                 let uu____13922 = FStar_Ident.string_of_lid msrc  in
                 let uu____13923 = FStar_Ident.string_of_lid mtgt  in
                 let uu____13924 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____13922
                   uu____13923 uu____13924);
            (let uu____13925 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____13925
             then
               let ed =
                 let uu____13927 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____13927  in
               let uu____13928 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____13928 with
               | (uu____13929,return_repr) ->
                   let return_inst =
                     let uu____13942 =
                       let uu____13943 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____13943.FStar_Syntax_Syntax.n  in
                     match uu____13942 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____13949::[]) ->
                         let uu____13954 =
                           let uu____13961 =
                             let uu____13962 =
                               let uu____13969 =
                                 let uu____13970 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____13970]  in
                               (return_tm, uu____13969)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____13962  in
                           FStar_Syntax_Syntax.mk uu____13961  in
                         uu____13954 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____13976 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____13979 =
                     let uu____13986 =
                       let uu____13987 =
                         let uu____14004 =
                           let uu____14015 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____14024 =
                             let uu____14035 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____14035]  in
                           uu____14015 :: uu____14024  in
                         (return_inst, uu____14004)  in
                       FStar_Syntax_Syntax.Tm_app uu____13987  in
                     FStar_Syntax_Syntax.mk uu____13986  in
                   uu____13979 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____14084 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____14084 with
                | FStar_Pervasives_Native.None  ->
                    let uu____14087 =
                      let uu____14088 = FStar_Ident.text_of_lid msrc  in
                      let uu____14089 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____14088 uu____14089
                       in
                    failwith uu____14087
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14090;
                      FStar_TypeChecker_Env.mtarget = uu____14091;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14092;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____14114 =
                      let uu____14115 = FStar_Ident.text_of_lid msrc  in
                      let uu____14116 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____14115 uu____14116
                       in
                    failwith uu____14114
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14117;
                      FStar_TypeChecker_Env.mtarget = uu____14118;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14119;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____14154 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____14155 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____14154 t FStar_Syntax_Syntax.tun uu____14155))

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
                (fun uu____14225  ->
                   match uu____14225 with
                   | (a,imp) ->
                       let uu____14244 = norm cfg env [] a  in
                       (uu____14244, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____14254  ->
             let uu____14255 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____14256 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____14255 uu____14256);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____14280 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____14280
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___320_14283 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___320_14283.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___320_14283.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____14305 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____14305
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___321_14308 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___321_14308.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___321_14308.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____14353  ->
                      match uu____14353 with
                      | (a,i) ->
                          let uu____14372 = norm cfg env [] a  in
                          (uu____14372, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___265_14394  ->
                       match uu___265_14394 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____14398 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____14398
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___322_14406 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___323_14409 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___323_14409.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___322_14406.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___322_14406.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun uu____14412  ->
        match uu____14412 with
        | (x,imp) ->
            let uu____14419 =
              let uu___324_14420 = x  in
              let uu____14421 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___324_14420.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___324_14420.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____14421
              }  in
            (uu____14419, imp)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____14429 =
          FStar_List.fold_left
            (fun uu____14463  ->
               fun b  ->
                 match uu____14463 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____14429 with | (nbs,uu____14543) -> FStar_List.rev nbs

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
            let uu____14575 =
              let uu___325_14576 = rc  in
              let uu____14577 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___325_14576.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____14577;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___325_14576.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____14575
        | uu____14586 -> lopt

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
            (let uu____14595 = FStar_Syntax_Print.term_to_string tm  in
             let uu____14596 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____14595 uu____14596)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___266_14600  ->
      match uu___266_14600 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____14613 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____14613 with
           | FStar_Pervasives_Native.Some (t,uu____14621) -> t
           | FStar_Pervasives_Native.None  ->
               let uu____14630 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____14630)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____14638 = norm_cb cfg  in
            reduce_primops uu____14638 cfg env tm  in
          let uu____14645 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____14645
          then tm1
          else
            (let w t =
               let uu___326_14659 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___326_14659.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___326_14659.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____14670 =
                 let uu____14671 = FStar_Syntax_Util.unmeta t  in
                 uu____14671.FStar_Syntax_Syntax.n  in
               match uu____14670 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____14678 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____14739)::args1,(bv,uu____14742)::bs1) ->
                   let uu____14796 =
                     let uu____14797 = FStar_Syntax_Subst.compress t  in
                     uu____14797.FStar_Syntax_Syntax.n  in
                   (match uu____14796 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____14801 -> false)
               | ([],[]) -> true
               | (uu____14830,uu____14831) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____14880 = FStar_Syntax_Print.term_to_string t  in
                  let uu____14881 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____14880
                    uu____14881)
               else ();
               (let uu____14883 = FStar_Syntax_Util.head_and_args' t  in
                match uu____14883 with
                | (hd1,args) ->
                    let uu____14922 =
                      let uu____14923 = FStar_Syntax_Subst.compress hd1  in
                      uu____14923.FStar_Syntax_Syntax.n  in
                    (match uu____14922 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____14930 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____14931 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____14932 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____14930 uu____14931 uu____14932)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____14934 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____14951 = FStar_Syntax_Print.term_to_string t  in
                  let uu____14952 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____14951
                    uu____14952)
               else ();
               (let uu____14954 = FStar_Syntax_Util.is_squash t  in
                match uu____14954 with
                | FStar_Pervasives_Native.Some (uu____14965,t') ->
                    is_applied bs t'
                | uu____14977 ->
                    let uu____14986 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____14986 with
                     | FStar_Pervasives_Native.Some (uu____14997,t') ->
                         is_applied bs t'
                     | uu____15009 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____15033 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____15033 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____15040)::(q,uu____15042)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____15084 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____15085 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____15084 uu____15085)
                    else ();
                    (let uu____15087 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____15087 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____15092 =
                           let uu____15093 = FStar_Syntax_Subst.compress p
                              in
                           uu____15093.FStar_Syntax_Syntax.n  in
                         (match uu____15092 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____15101 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____15101))
                          | uu____15104 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____15107)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____15132 =
                           let uu____15133 = FStar_Syntax_Subst.compress p1
                              in
                           uu____15133.FStar_Syntax_Syntax.n  in
                         (match uu____15132 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____15141 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____15141))
                          | uu____15144 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____15148 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____15148 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____15153 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____15153 with
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
                                     let uu____15164 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____15164))
                               | uu____15167 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____15172)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____15197 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____15197 with
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
                                     let uu____15208 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____15208))
                               | uu____15211 -> FStar_Pervasives_Native.None)
                          | uu____15214 -> FStar_Pervasives_Native.None)
                     | uu____15217 -> FStar_Pervasives_Native.None))
               | uu____15220 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____15233 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____15233 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____15239)::[],uu____15240,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____15259 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____15260 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____15259
                         uu____15260)
                    else ();
                    is_quantified_const bv phi')
               | uu____15262 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____15275 =
                 let uu____15276 = FStar_Syntax_Subst.compress phi  in
                 uu____15276.FStar_Syntax_Syntax.n  in
               match uu____15275 with
               | FStar_Syntax_Syntax.Tm_match (uu____15281,br::brs) ->
                   let uu____15348 = br  in
                   (match uu____15348 with
                    | (uu____15365,uu____15366,e) ->
                        let r =
                          let uu____15387 = simp_t e  in
                          match uu____15387 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____15393 =
                                FStar_List.for_all
                                  (fun uu____15411  ->
                                     match uu____15411 with
                                     | (uu____15424,uu____15425,e') ->
                                         let uu____15439 = simp_t e'  in
                                         uu____15439 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____15393
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____15447 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____15456 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____15456
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____15491 =
                 match uu____15491 with
                 | (t1,q) ->
                     let uu____15512 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____15512 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____15544 -> (t1, q))
                  in
               let uu____15557 = FStar_Syntax_Util.head_and_args t  in
               match uu____15557 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____15635 =
                 let uu____15636 = FStar_Syntax_Util.unmeta ty  in
                 uu____15636.FStar_Syntax_Syntax.n  in
               match uu____15635 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____15640) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____15645,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____15669 -> false  in
             let simplify1 arg =
               let uu____15700 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____15700, arg)  in
             let uu____15713 = is_forall_const tm1  in
             match uu____15713 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____15718 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____15719 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____15718
                       uu____15719)
                  else ();
                  (let uu____15721 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____15721))
             | FStar_Pervasives_Native.None  ->
                 let uu____15722 =
                   let uu____15723 = FStar_Syntax_Subst.compress tm1  in
                   uu____15723.FStar_Syntax_Syntax.n  in
                 (match uu____15722 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____15727;
                              FStar_Syntax_Syntax.vars = uu____15728;_},uu____15729);
                         FStar_Syntax_Syntax.pos = uu____15730;
                         FStar_Syntax_Syntax.vars = uu____15731;_},args)
                      ->
                      let uu____15761 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____15761
                      then
                        let uu____15762 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____15762 with
                         | (FStar_Pervasives_Native.Some (true ),uu____15817)::
                             (uu____15818,(arg,uu____15820))::[] ->
                             maybe_auto_squash arg
                         | (uu____15885,(arg,uu____15887))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____15888)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____15953)::uu____15954::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____16017::(FStar_Pervasives_Native.Some (false
                                         ),uu____16018)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____16081 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____16097 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____16097
                         then
                           let uu____16098 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____16098 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____16153)::uu____16154::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____16217::(FStar_Pervasives_Native.Some (true
                                           ),uu____16218)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____16281)::(uu____16282,(arg,uu____16284))::[]
                               -> maybe_auto_squash arg
                           | (uu____16349,(arg,uu____16351))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____16352)::[]
                               -> maybe_auto_squash arg
                           | uu____16417 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____16433 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____16433
                            then
                              let uu____16434 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____16434 with
                              | uu____16489::(FStar_Pervasives_Native.Some
                                              (true ),uu____16490)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____16553)::uu____16554::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____16617)::(uu____16618,(arg,uu____16620))::[]
                                  -> maybe_auto_squash arg
                              | (uu____16685,(p,uu____16687))::(uu____16688,
                                                                (q,uu____16690))::[]
                                  ->
                                  let uu____16755 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____16755
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____16757 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____16773 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____16773
                               then
                                 let uu____16774 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____16774 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16829)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____16830)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____16895)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____16896)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16961)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____16962)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17027)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17028)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____17093,(arg,uu____17095))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____17096)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17161)::(uu____17162,(arg,uu____17164))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____17229,(arg,uu____17231))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____17232)::[]
                                     ->
                                     let uu____17297 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17297
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17298)::(uu____17299,(arg,uu____17301))::[]
                                     ->
                                     let uu____17366 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17366
                                 | (uu____17367,(p,uu____17369))::(uu____17370,
                                                                   (q,uu____17372))::[]
                                     ->
                                     let uu____17437 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____17437
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____17439 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____17455 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____17455
                                  then
                                    let uu____17456 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____17456 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____17511)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____17550)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____17589 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____17605 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____17605
                                     then
                                       match args with
                                       | (t,uu____17607)::[] ->
                                           let uu____17632 =
                                             let uu____17633 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17633.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17632 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17636::[],body,uu____17638)
                                                ->
                                                let uu____17673 = simp_t body
                                                   in
                                                (match uu____17673 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____17676 -> tm1)
                                            | uu____17679 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____17681))::(t,uu____17683)::[]
                                           ->
                                           let uu____17722 =
                                             let uu____17723 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17723.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17722 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17726::[],body,uu____17728)
                                                ->
                                                let uu____17763 = simp_t body
                                                   in
                                                (match uu____17763 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____17766 -> tm1)
                                            | uu____17769 -> tm1)
                                       | uu____17770 -> tm1
                                     else
                                       (let uu____17782 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____17782
                                        then
                                          match args with
                                          | (t,uu____17784)::[] ->
                                              let uu____17809 =
                                                let uu____17810 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17810.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17809 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17813::[],body,uu____17815)
                                                   ->
                                                   let uu____17850 =
                                                     simp_t body  in
                                                   (match uu____17850 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____17853 -> tm1)
                                               | uu____17856 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____17858))::(t,uu____17860)::[]
                                              ->
                                              let uu____17899 =
                                                let uu____17900 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17900.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17899 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17903::[],body,uu____17905)
                                                   ->
                                                   let uu____17940 =
                                                     simp_t body  in
                                                   (match uu____17940 with
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
                                                    | uu____17943 -> tm1)
                                               | uu____17946 -> tm1)
                                          | uu____17947 -> tm1
                                        else
                                          (let uu____17959 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____17959
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____17960;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____17961;_},uu____17962)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____17987;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____17988;_},uu____17989)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____18014 -> tm1
                                           else
                                             (let uu____18026 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____18026 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____18046 ->
                                                  let uu____18055 =
                                                    let uu____18062 =
                                                      norm_cb cfg  in
                                                    reduce_equality
                                                      uu____18062 cfg env
                                                     in
                                                  uu____18055 tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____18070;
                         FStar_Syntax_Syntax.vars = uu____18071;_},args)
                      ->
                      let uu____18097 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18097
                      then
                        let uu____18098 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18098 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18153)::
                             (uu____18154,(arg,uu____18156))::[] ->
                             maybe_auto_squash arg
                         | (uu____18221,(arg,uu____18223))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18224)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18289)::uu____18290::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18353::(FStar_Pervasives_Native.Some (false
                                         ),uu____18354)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18417 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18433 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18433
                         then
                           let uu____18434 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18434 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18489)::uu____18490::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18553::(FStar_Pervasives_Native.Some (true
                                           ),uu____18554)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18617)::(uu____18618,(arg,uu____18620))::[]
                               -> maybe_auto_squash arg
                           | (uu____18685,(arg,uu____18687))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18688)::[]
                               -> maybe_auto_squash arg
                           | uu____18753 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18769 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____18769
                            then
                              let uu____18770 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____18770 with
                              | uu____18825::(FStar_Pervasives_Native.Some
                                              (true ),uu____18826)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____18889)::uu____18890::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____18953)::(uu____18954,(arg,uu____18956))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19021,(p,uu____19023))::(uu____19024,
                                                                (q,uu____19026))::[]
                                  ->
                                  let uu____19091 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19091
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19093 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19109 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19109
                               then
                                 let uu____19110 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19110 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19165)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19166)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19231)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19232)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19297)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19298)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19363)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19364)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19429,(arg,uu____19431))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19432)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19497)::(uu____19498,(arg,uu____19500))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19565,(arg,uu____19567))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19568)::[]
                                     ->
                                     let uu____19633 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19633
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19634)::(uu____19635,(arg,uu____19637))::[]
                                     ->
                                     let uu____19702 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19702
                                 | (uu____19703,(p,uu____19705))::(uu____19706,
                                                                   (q,uu____19708))::[]
                                     ->
                                     let uu____19773 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19773
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19775 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19791 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19791
                                  then
                                    let uu____19792 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19792 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19847)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19886)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19925 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19941 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19941
                                     then
                                       match args with
                                       | (t,uu____19943)::[] ->
                                           let uu____19968 =
                                             let uu____19969 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19969.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19968 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19972::[],body,uu____19974)
                                                ->
                                                let uu____20009 = simp_t body
                                                   in
                                                (match uu____20009 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20012 -> tm1)
                                            | uu____20015 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20017))::(t,uu____20019)::[]
                                           ->
                                           let uu____20058 =
                                             let uu____20059 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20059.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20058 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20062::[],body,uu____20064)
                                                ->
                                                let uu____20099 = simp_t body
                                                   in
                                                (match uu____20099 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20102 -> tm1)
                                            | uu____20105 -> tm1)
                                       | uu____20106 -> tm1
                                     else
                                       (let uu____20118 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20118
                                        then
                                          match args with
                                          | (t,uu____20120)::[] ->
                                              let uu____20145 =
                                                let uu____20146 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20146.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20145 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20149::[],body,uu____20151)
                                                   ->
                                                   let uu____20186 =
                                                     simp_t body  in
                                                   (match uu____20186 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20189 -> tm1)
                                               | uu____20192 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20194))::(t,uu____20196)::[]
                                              ->
                                              let uu____20235 =
                                                let uu____20236 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20236.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20235 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20239::[],body,uu____20241)
                                                   ->
                                                   let uu____20276 =
                                                     simp_t body  in
                                                   (match uu____20276 with
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
                                                    | uu____20279 -> tm1)
                                               | uu____20282 -> tm1)
                                          | uu____20283 -> tm1
                                        else
                                          (let uu____20295 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20295
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20296;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20297;_},uu____20298)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20323;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20324;_},uu____20325)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20350 -> tm1
                                           else
                                             (let uu____20362 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20362 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20382 ->
                                                  let uu____20391 =
                                                    let uu____20398 =
                                                      norm_cb cfg  in
                                                    reduce_equality
                                                      uu____20398 cfg env
                                                     in
                                                  uu____20391 tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____20411 = simp_t t  in
                      (match uu____20411 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____20414 ->
                      let uu____20437 = is_const_match tm1  in
                      (match uu____20437 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____20440 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____20450  ->
               (let uu____20452 = FStar_Syntax_Print.tag_of_term t  in
                let uu____20453 = FStar_Syntax_Print.term_to_string t  in
                let uu____20454 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____20461 =
                  let uu____20462 =
                    let uu____20465 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____20465
                     in
                  stack_to_string uu____20462  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____20452 uu____20453 uu____20454 uu____20461);
               (let uu____20488 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____20488
                then
                  let uu____20489 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____20489 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____20496 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____20497 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____20498 =
                          let uu____20499 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____20499
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____20496
                          uu____20497 uu____20498);
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
                   let uu____20517 =
                     let uu____20518 =
                       let uu____20519 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____20519  in
                     FStar_Util.string_of_int uu____20518  in
                   let uu____20524 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____20525 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____20517 uu____20524 uu____20525)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____20531,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                FStar_TypeChecker_Cfg.log cfg
                  (fun uu____20582  ->
                     let uu____20583 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____20583);
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
               let uu____20621 =
                 let uu___327_20622 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___327_20622.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___327_20622.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____20621
           | (Arg (Univ uu____20625,uu____20626,uu____20627))::uu____20628 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____20631,uu____20632))::uu____20633 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____20648,uu____20649),aq,r))::stack1
               when
               let uu____20699 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____20699 ->
               let t2 =
                 let uu____20703 =
                   let uu____20708 =
                     let uu____20709 = closure_as_term cfg env_arg tm  in
                     (uu____20709, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____20708  in
                 uu____20703 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____20721),aq,r))::stack1 ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____20774  ->
                     let uu____20775 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____20775);
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
                  (let uu____20789 = FStar_ST.op_Bang m  in
                   match uu____20789 with
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
                   | FStar_Pervasives_Native.Some (uu____20930,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____20985 =
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____20989  ->
                      let uu____20990 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____20990);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____20998 =
                 let uu____20999 = FStar_Syntax_Subst.compress t1  in
                 uu____20999.FStar_Syntax_Syntax.n  in
               (match uu____20998 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____21026 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____21026  in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____21030  ->
                          let uu____21031 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____21031);
                     (let uu____21032 = FStar_List.tl stack  in
                      norm cfg env1 uu____21032 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____21033);
                       FStar_Syntax_Syntax.pos = uu____21034;
                       FStar_Syntax_Syntax.vars = uu____21035;_},(e,uu____21037)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____21076 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                    ->
                    let uu____21093 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____21093 with
                     | (hd1,args) ->
                         let uu____21136 =
                           let uu____21137 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____21137.FStar_Syntax_Syntax.n  in
                         (match uu____21136 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____21141 =
                                FStar_TypeChecker_Cfg.find_prim_step cfg fv
                                 in
                              (match uu____21141 with
                               | FStar_Pervasives_Native.Some
                                   {
                                     FStar_TypeChecker_Cfg.name = uu____21144;
                                     FStar_TypeChecker_Cfg.arity =
                                       uu____21145;
                                     FStar_TypeChecker_Cfg.univ_arity =
                                       uu____21146;
                                     FStar_TypeChecker_Cfg.auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     FStar_TypeChecker_Cfg.strong_reduction_ok
                                       = uu____21148;
                                     FStar_TypeChecker_Cfg.requires_binder_substitution
                                       = uu____21149;
                                     FStar_TypeChecker_Cfg.interpretation =
                                       uu____21150;
                                     FStar_TypeChecker_Cfg.interpretation_nbe
                                       = uu____21151;_}
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
                             (fun uu___267_21283  ->
                                match uu___267_21283 with
                                | FStar_TypeChecker_Env.InliningDelta  ->
                                    true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____21284 -> false))
                         in
                      let steps =
                        let uu___328_21286 = cfg1.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___328_21286.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___328_21286.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta = false;
                          FStar_TypeChecker_Cfg.weak =
                            (uu___328_21286.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___328_21286.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___328_21286.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___328_21286.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___328_21286.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_tac = false;
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___328_21286.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___328_21286.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___328_21286.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___328_21286.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___328_21286.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___328_21286.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___328_21286.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___328_21286.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___328_21286.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___328_21286.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___328_21286.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___328_21286.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___328_21286.FStar_TypeChecker_Cfg.nbe_step)
                        }  in
                      let uu___329_21291 = cfg1  in
                      {
                        FStar_TypeChecker_Cfg.steps = steps;
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___329_21291.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___329_21291.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level = new_delta;
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___329_21291.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong = true;
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___329_21291.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___329_21291.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying =
                          (uu___329_21291.FStar_TypeChecker_Cfg.reifying)
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
                               ((let uu___330_21778 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___330_21778.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___331_21797 = x  in
                            let uu____21798 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___331_21797.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___331_21797.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21798
                            }  in
                          ((let uu___332_21812 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___332_21812.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___333_21823 = x  in
                            let uu____21824 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___333_21823.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___333_21823.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21824
                            }  in
                          ((let uu___334_21838 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___334_21838.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___335_21854 = x  in
                            let uu____21855 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___335_21854.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___335_21854.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21855
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___336_21870 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___336_21870.FStar_Syntax_Syntax.p)
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
                          (let uu___337_22041 = cfg1  in
                           {
                             FStar_TypeChecker_Cfg.steps =
                               (let uu___338_22044 =
                                  cfg1.FStar_TypeChecker_Cfg.steps  in
                                {
                                  FStar_TypeChecker_Cfg.beta =
                                    (uu___338_22044.FStar_TypeChecker_Cfg.beta);
                                  FStar_TypeChecker_Cfg.iota =
                                    (uu___338_22044.FStar_TypeChecker_Cfg.iota);
                                  FStar_TypeChecker_Cfg.zeta =
                                    (uu___338_22044.FStar_TypeChecker_Cfg.zeta);
                                  FStar_TypeChecker_Cfg.weak =
                                    (uu___338_22044.FStar_TypeChecker_Cfg.weak);
                                  FStar_TypeChecker_Cfg.hnf =
                                    (uu___338_22044.FStar_TypeChecker_Cfg.hnf);
                                  FStar_TypeChecker_Cfg.primops =
                                    (uu___338_22044.FStar_TypeChecker_Cfg.primops);
                                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                    =
                                    (uu___338_22044.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                  FStar_TypeChecker_Cfg.unfold_until =
                                    (uu___338_22044.FStar_TypeChecker_Cfg.unfold_until);
                                  FStar_TypeChecker_Cfg.unfold_only =
                                    (uu___338_22044.FStar_TypeChecker_Cfg.unfold_only);
                                  FStar_TypeChecker_Cfg.unfold_fully =
                                    (uu___338_22044.FStar_TypeChecker_Cfg.unfold_fully);
                                  FStar_TypeChecker_Cfg.unfold_attr =
                                    (uu___338_22044.FStar_TypeChecker_Cfg.unfold_attr);
                                  FStar_TypeChecker_Cfg.unfold_tac =
                                    (uu___338_22044.FStar_TypeChecker_Cfg.unfold_tac);
                                  FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                    =
                                    (uu___338_22044.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                  FStar_TypeChecker_Cfg.simplify =
                                    (uu___338_22044.FStar_TypeChecker_Cfg.simplify);
                                  FStar_TypeChecker_Cfg.erase_universes =
                                    (uu___338_22044.FStar_TypeChecker_Cfg.erase_universes);
                                  FStar_TypeChecker_Cfg.allow_unbound_universes
                                    =
                                    (uu___338_22044.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                  FStar_TypeChecker_Cfg.reify_ =
                                    (uu___338_22044.FStar_TypeChecker_Cfg.reify_);
                                  FStar_TypeChecker_Cfg.compress_uvars =
                                    (uu___338_22044.FStar_TypeChecker_Cfg.compress_uvars);
                                  FStar_TypeChecker_Cfg.no_full_norm =
                                    (uu___338_22044.FStar_TypeChecker_Cfg.no_full_norm);
                                  FStar_TypeChecker_Cfg.check_no_uvars =
                                    (uu___338_22044.FStar_TypeChecker_Cfg.check_no_uvars);
                                  FStar_TypeChecker_Cfg.unmeta =
                                    (uu___338_22044.FStar_TypeChecker_Cfg.unmeta);
                                  FStar_TypeChecker_Cfg.unascribe =
                                    (uu___338_22044.FStar_TypeChecker_Cfg.unascribe);
                                  FStar_TypeChecker_Cfg.in_full_norm_request
                                    =
                                    (uu___338_22044.FStar_TypeChecker_Cfg.in_full_norm_request);
                                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                    = false;
                                  FStar_TypeChecker_Cfg.nbe_step =
                                    (uu___338_22044.FStar_TypeChecker_Cfg.nbe_step)
                                });
                             FStar_TypeChecker_Cfg.tcenv =
                               (uu___337_22041.FStar_TypeChecker_Cfg.tcenv);
                             FStar_TypeChecker_Cfg.debug =
                               (uu___337_22041.FStar_TypeChecker_Cfg.debug);
                             FStar_TypeChecker_Cfg.delta_level =
                               (uu___337_22041.FStar_TypeChecker_Cfg.delta_level);
                             FStar_TypeChecker_Cfg.primitive_steps =
                               (uu___337_22041.FStar_TypeChecker_Cfg.primitive_steps);
                             FStar_TypeChecker_Cfg.strong =
                               (uu___337_22041.FStar_TypeChecker_Cfg.strong);
                             FStar_TypeChecker_Cfg.memoize_lazy =
                               (uu___337_22041.FStar_TypeChecker_Cfg.memoize_lazy);
                             FStar_TypeChecker_Cfg.normalize_pure_lets =
                               (uu___337_22041.FStar_TypeChecker_Cfg.normalize_pure_lets);
                             FStar_TypeChecker_Cfg.reifying =
                               (uu___337_22041.FStar_TypeChecker_Cfg.reifying)
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
          let uu___339_23184 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___339_23184.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___339_23184.FStar_Syntax_Syntax.vars)
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
                  let uu___340_23204 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___340_23204.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___340_23204.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___340_23204.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev
                      cfg.FStar_TypeChecker_Cfg.tcenv c
                     in
                  let uu___341_23206 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___341_23206.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___341_23206.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___341_23206.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___341_23206.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___342_23207 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___342_23207.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___342_23207.FStar_Syntax_Syntax.vars)
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
          (fun uu___344_23256  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___343_23259 ->
            ((let uu____23261 =
                let uu____23266 =
                  let uu____23267 = FStar_Util.message_of_exn uu___343_23259
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
          (fun uu___346_23281  ->
             match () with
             | () ->
                 let uu____23282 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____23282 [] c) ()
        with
        | uu___345_23291 ->
            ((let uu____23293 =
                let uu____23298 =
                  let uu____23299 = FStar_Util.message_of_exn uu___345_23291
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
                                (let uu___347_23664 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___347_23664.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___347_23664.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___347_23664.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___347_23664.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___347_23664.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___347_23664.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___347_23664.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___347_23664.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___347_23664.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___347_23664.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___347_23664.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___347_23664.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___347_23664.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___347_23664.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___347_23664.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___347_23664.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___347_23664.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___347_23664.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___347_23664.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___347_23664.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___347_23664.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___347_23664.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___347_23664.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___347_23664.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___347_23664.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___347_23664.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___347_23664.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___347_23664.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___347_23664.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___347_23664.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___347_23664.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___347_23664.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___347_23664.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___347_23664.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___347_23664.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___347_23664.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___347_23664.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___347_23664.FStar_TypeChecker_Env.dep_graph);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___347_23664.FStar_TypeChecker_Env.nbe)
                                 }) t
                               in
                            match uu____23656 with
                            | (uu____23665,ty,uu____23667) ->
                                eta_expand_with_type env t ty))
                | uu____23668 ->
                    let uu____23669 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___348_23677 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___348_23677.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___348_23677.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___348_23677.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___348_23677.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___348_23677.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___348_23677.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___348_23677.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___348_23677.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___348_23677.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___348_23677.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___348_23677.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___348_23677.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___348_23677.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___348_23677.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___348_23677.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___348_23677.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___348_23677.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___348_23677.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___348_23677.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___348_23677.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___348_23677.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___348_23677.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___348_23677.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___348_23677.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___348_23677.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___348_23677.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___348_23677.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___348_23677.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___348_23677.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___348_23677.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___348_23677.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___348_23677.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___348_23677.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___348_23677.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___348_23677.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___348_23677.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___348_23677.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___348_23677.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___348_23677.FStar_TypeChecker_Env.nbe)
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
      let uu___349_23761 = x  in
      let uu____23762 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___349_23761.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___349_23761.FStar_Syntax_Syntax.index);
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
          let uu___350_23834 = rc  in
          let uu____23835 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____23844 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___350_23834.FStar_Syntax_Syntax.residual_effect);
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
              let uu___351_24093 = p  in
              let uu____24094 =
                let uu____24095 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____24095  in
              {
                FStar_Syntax_Syntax.v = uu____24094;
                FStar_Syntax_Syntax.p =
                  (uu___351_24093.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___352_24097 = p  in
              let uu____24098 =
                let uu____24099 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____24099  in
              {
                FStar_Syntax_Syntax.v = uu____24098;
                FStar_Syntax_Syntax.p =
                  (uu___352_24097.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___353_24106 = p  in
              let uu____24107 =
                let uu____24108 =
                  let uu____24115 = elim_bv x  in
                  let uu____24116 = elim_delayed_subst_term t0  in
                  (uu____24115, uu____24116)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____24108  in
              {
                FStar_Syntax_Syntax.v = uu____24107;
                FStar_Syntax_Syntax.p =
                  (uu___353_24106.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___354_24139 = p  in
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
                  (uu___354_24139.FStar_Syntax_Syntax.p)
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
          let uu___355_24571 = lb  in
          let uu____24572 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____24575 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___355_24571.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___355_24571.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____24572;
            FStar_Syntax_Syntax.lbeff =
              (uu___355_24571.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____24575;
            FStar_Syntax_Syntax.lbattrs =
              (uu___355_24571.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___355_24571.FStar_Syntax_Syntax.lbpos)
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
      (fun uu___268_24691  ->
         match uu___268_24691 with
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
          let uu___356_24764 = ct  in
          let uu____24765 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____24768 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____24779 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___356_24764.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___356_24764.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____24765;
            FStar_Syntax_Syntax.effect_args = uu____24768;
            FStar_Syntax_Syntax.flags = uu____24779
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___269_24782  ->
    match uu___269_24782 with
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
               let uu___357_24963 = x  in
               let uu____24964 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___357_24963.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___357_24963.FStar_Syntax_Syntax.index);
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
               let uu___358_25851 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___358_25851.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___358_25851.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___358_25851.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___358_25851.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___359_25866 = s  in
          let uu____25867 =
            let uu____25868 =
              let uu____25877 = FStar_List.map (elim_uvars env) sigs  in
              (uu____25877, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____25868  in
          {
            FStar_Syntax_Syntax.sigel = uu____25867;
            FStar_Syntax_Syntax.sigrng =
              (uu___359_25866.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___359_25866.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___359_25866.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___359_25866.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____25894 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25894 with
           | (univ_names1,uu____25918,typ1) ->
               let uu___360_25940 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___360_25940.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___360_25940.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___360_25940.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___360_25940.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____25946 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25946 with
           | (univ_names1,uu____25970,typ1) ->
               let uu___361_25992 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___361_25992.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___361_25992.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___361_25992.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___361_25992.FStar_Syntax_Syntax.sigattrs)
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
                        let uu___362_26050 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___362_26050.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___362_26050.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___362_26050.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___362_26050.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___363_26051 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___363_26051.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___363_26051.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___363_26051.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___363_26051.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___364_26057 = s  in
          let uu____26058 =
            let uu____26059 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____26059  in
          {
            FStar_Syntax_Syntax.sigel = uu____26058;
            FStar_Syntax_Syntax.sigrng =
              (uu___364_26057.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___364_26057.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___364_26057.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___364_26057.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____26063 = elim_uvars_aux_t env us [] t  in
          (match uu____26063 with
           | (us1,uu____26087,t1) ->
               let uu___365_26109 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___365_26109.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___365_26109.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___365_26109.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___365_26109.FStar_Syntax_Syntax.sigattrs)
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
                                      let uu___366_26832 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___366_26832.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___366_26832.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___367_26834 = ed  in
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
                               (uu___367_26834.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___367_26834.FStar_Syntax_Syntax.mname);
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
                               (uu___367_26834.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___368_26851 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___368_26851.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___368_26851.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___368_26851.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___368_26851.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___270_26872 =
            match uu___270_26872 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____26903 = elim_uvars_aux_t env us [] t  in
                (match uu____26903 with
                 | (us1,uu____26935,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___369_26966 = sub_eff  in
            let uu____26967 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____26970 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___369_26966.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___369_26966.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____26967;
              FStar_Syntax_Syntax.lift = uu____26970
            }  in
          let uu___370_26973 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___370_26973.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___370_26973.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___370_26973.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___370_26973.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____26983 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____26983 with
           | (univ_names1,binders1,comp1) ->
               let uu___371_27023 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___371_27023.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___371_27023.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___371_27023.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___371_27023.FStar_Syntax_Syntax.sigattrs)
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
  