open Prims
let cases :
  'Auu____11 'Auu____12 .
    ('Auu____11 -> 'Auu____12) ->
      'Auu____12 -> 'Auu____11 FStar_Pervasives_Native.option -> 'Auu____12
  =
  fun f  ->
    fun d  ->
      fun uu___248_32  ->
        match uu___248_32 with
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
  fun uu___249_1097  ->
    match uu___249_1097 with
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
  fun uu___250_1159  ->
    match uu___250_1159 with
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
  fun uu___251_1249  ->
    match uu___251_1249 with | [] -> true | uu____1252 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        (fun uu___269_1283  ->
           match () with
           | () ->
               let uu____1284 =
                 FStar_List.nth env x.FStar_Syntax_Syntax.index  in
               FStar_Pervasives_Native.snd uu____1284) ()
      with
      | uu___268_1301 ->
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
                 (fun uu___271_1463  ->
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
                                      (fun uu___252_1859  ->
                                         match uu___252_1859 with
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
                                                 (let uu___272_1883 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___272_1883.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___272_1883.FStar_Syntax_Syntax.sort)
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
                         let uu___273_1895 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___273_1895.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___273_1895.FStar_Syntax_Syntax.vars)
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
                           let uu___274_1934 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___274_1934.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___274_1934.FStar_Syntax_Syntax.index);
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
                             (let uu___275_2734 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___275_2734.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___275_2734.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____2718))
                       in
                    (match uu____2688 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___276_2752 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___276_2752.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___276_2752.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___276_2752.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___276_2752.FStar_Syntax_Syntax.lbpos)
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
                             (let uu___277_2890 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___277_2890.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___277_2890.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___278_2891 = lb  in
                      let uu____2892 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___278_2891.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___278_2891.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____2892;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___278_2891.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___278_2891.FStar_Syntax_Syntax.lbpos)
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
                      let uu___279_3141 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___279_3141.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___279_3141.FStar_Syntax_Syntax.vars)
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
                                ((let uu___280_3727 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___280_3727.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___281_3746 = x  in
                             let uu____3747 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___281_3746.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___281_3746.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3747
                             }  in
                           ((let uu___282_3761 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___282_3761.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___283_3772 = x  in
                             let uu____3773 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___283_3772.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___283_3772.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3773
                             }  in
                           ((let uu___284_3787 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___284_3787.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___285_3803 = x  in
                             let uu____3804 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___285_3803.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___285_3803.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3804
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___286_3821 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___286_3821.FStar_Syntax_Syntax.p)
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
                          let uu___287_4481 = b  in
                          let uu____4482 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___287_4481.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___287_4481.FStar_Syntax_Syntax.index);
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
                        (fun uu___253_4739  ->
                           match uu___253_4739 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4743 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____4743
                           | f -> f))
                    in
                 let uu____4747 =
                   let uu___288_4748 = c1  in
                   let uu____4749 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4749;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___288_4748.FStar_Syntax_Syntax.effect_name);
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
         (fun uu___254_4759  ->
            match uu___254_4759 with
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
                   (fun uu___255_4781  ->
                      match uu___255_4781 with
                      | FStar_Syntax_Syntax.DECREASES uu____4782 -> false
                      | uu____4785 -> true))
               in
            let rc1 =
              let uu___289_4787 = rc  in
              let uu____4788 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___289_4787.FStar_Syntax_Syntax.residual_effect);
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
                                      let uu___290_5109 = bv  in
                                      let uu____5110 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___290_5109.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___290_5109.FStar_Syntax_Syntax.index);
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
                                      (fun uu___256_5139  ->
                                         match uu___256_5139 with
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
          (let uu___291_5660 = cfg  in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___292_5663 = FStar_TypeChecker_Cfg.default_steps  in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___292_5663.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___292_5663.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___292_5663.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___292_5663.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___292_5663.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___292_5663.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___292_5663.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___292_5663.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___292_5663.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___292_5663.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___292_5663.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___292_5663.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___292_5663.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___292_5663.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___292_5663.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___292_5663.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___292_5663.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___292_5663.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___292_5663.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___292_5663.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___292_5663.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___292_5663.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___292_5663.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___292_5663.FStar_TypeChecker_Cfg.nbe_step)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___291_5660.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___291_5660.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___291_5660.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___291_5660.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___291_5660.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___291_5660.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___291_5660.FStar_TypeChecker_Cfg.reifying)
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
  fun uu___257_5735  ->
    match uu___257_5735 with
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
                 (fun uu___258_6053  ->
                    match uu___258_6053 with
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
  fun uu___259_6098  ->
    match uu___259_6098 with
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
                              (fun uu___260_7916  ->
                                 match uu___260_7916 with
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
                    let uu___293_8031 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___294_8034 = cfg.FStar_TypeChecker_Cfg.steps
                            in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___294_8034.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___294_8034.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___294_8034.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___294_8034.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___294_8034.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___294_8034.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___294_8034.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___294_8034.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___294_8034.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___294_8034.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___294_8034.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___294_8034.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___294_8034.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___294_8034.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___294_8034.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___294_8034.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___294_8034.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___294_8034.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___294_8034.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___294_8034.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___294_8034.FStar_TypeChecker_Cfg.nbe_step)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___293_8031.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___293_8031.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___293_8031.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___293_8031.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___293_8031.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___293_8031.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___293_8031.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___293_8031.FStar_TypeChecker_Cfg.reifying)
                    }  in
                  let stack' =
                    match stack with
                    | (UnivArgs i)::stack' -> (UnivArgs i) :: (Cfg cfg) ::
                        stack'
                    | stack' -> (Cfg cfg) :: stack'  in
                  FStar_Pervasives_Native.Some (cfg', stack')
              | Should_unfold_reify  ->
                  let uu____8067 =
                    let uu____8074 = FStar_List.tl stack  in
                    (cfg, uu____8074)  in
                  FStar_Pervasives_Native.Some uu____8067
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____8361 ->
                   let uu____8384 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____8384
               | uu____8385 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____8394  ->
               let uu____8395 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____8396 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____8397 = FStar_Syntax_Print.term_to_string t1  in
               let uu____8398 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____8405 =
                 let uu____8406 =
                   let uu____8409 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8409
                    in
                 stack_to_string uu____8406  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____8395 uu____8396 uu____8397 uu____8398 uu____8405);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____8435  ->
               let uu____8436 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____8436);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8440  ->
                     let uu____8441 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8441);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____8442 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8446  ->
                     let uu____8447 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8447);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____8448 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8452  ->
                     let uu____8453 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8453);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____8454 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8458  ->
                     let uu____8459 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8459);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8460;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_17;
                 FStar_Syntax_Syntax.fv_qual = uu____8461;_}
               when _0_17 = (Prims.parse_int "0") ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8467  ->
                     let uu____8468 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8468);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8469;
                 FStar_Syntax_Syntax.fv_delta = uu____8470;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8474  ->
                     let uu____8475 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8475);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8476;
                 FStar_Syntax_Syntax.fv_delta = uu____8477;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____8478);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8488  ->
                     let uu____8489 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8489);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____8492 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv uu____8492
                  in
               let uu____8493 =
                 decide_unfolding cfg env stack t1.FStar_Syntax_Syntax.pos fv
                   qninfo
                  in
               (match uu____8493 with
                | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                    do_unfold_fv cfg1 env stack1 t1 qninfo fv
                | FStar_Pervasives_Native.None  -> rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_quoted uu____8520 ->
               let uu____8527 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____8527
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
                  && (is_norm_request hd1 args))
                 &&
                 (let uu____8563 =
                    FStar_Ident.lid_equals
                      (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____8563)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___295_8567 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___296_8570 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___296_8570.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___296_8570.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___296_8570.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___296_8570.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___296_8570.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___296_8570.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___296_8570.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___296_8570.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___296_8570.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___296_8570.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___296_8570.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___296_8570.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___296_8570.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___296_8570.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___296_8570.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___296_8570.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___296_8570.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___296_8570.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___296_8570.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___296_8570.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___296_8570.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___296_8570.FStar_TypeChecker_Cfg.nbe_step)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___295_8567.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___295_8567.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___295_8567.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___295_8567.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___295_8567.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___295_8567.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____8575 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____8575 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____8608  ->
                                 fun stack1  ->
                                   match uu____8608 with
                                   | (a,aq) ->
                                       let uu____8620 =
                                         let uu____8621 =
                                           let uu____8628 =
                                             let uu____8629 =
                                               let uu____8660 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____8660, false)
                                                in
                                             Clos uu____8629  in
                                           (uu____8628, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____8621  in
                                       uu____8620 :: stack1) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____8748  ->
                            let uu____8749 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____8749);
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
                        (let uu____8785 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting norm request on %s ... \n" uu____8785)
                      else ();
                      (let delta_level =
                         let uu____8790 =
                           FStar_All.pipe_right s
                             (FStar_Util.for_some
                                (fun uu___261_8795  ->
                                   match uu___261_8795 with
                                   | FStar_TypeChecker_Env.UnfoldUntil
                                       uu____8796 -> true
                                   | FStar_TypeChecker_Env.UnfoldOnly
                                       uu____8797 -> true
                                   | FStar_TypeChecker_Env.UnfoldFully
                                       uu____8800 -> true
                                   | uu____8803 -> false))
                            in
                         if uu____8790
                         then
                           [FStar_TypeChecker_Env.Unfold
                              FStar_Syntax_Syntax.delta_constant]
                         else [FStar_TypeChecker_Env.NoDelta]  in
                       let cfg'1 =
                         let uu___297_8808 = cfg  in
                         let uu____8809 =
                           let uu___298_8810 =
                             FStar_TypeChecker_Cfg.to_fsteps s  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___298_8810.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___298_8810.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___298_8810.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak =
                               (uu___298_8810.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___298_8810.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___298_8810.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___298_8810.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___298_8810.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               (uu___298_8810.FStar_TypeChecker_Cfg.unfold_only);
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___298_8810.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___298_8810.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___298_8810.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___298_8810.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___298_8810.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___298_8810.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___298_8810.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___298_8810.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___298_8810.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___298_8810.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___298_8810.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___298_8810.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___298_8810.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               true;
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___298_8810.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___298_8810.FStar_TypeChecker_Cfg.nbe_step)
                           }  in
                         {
                           FStar_TypeChecker_Cfg.steps = uu____8809;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___297_8808.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___297_8808.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = delta_level;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___297_8808.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong =
                             (uu___297_8808.FStar_TypeChecker_Cfg.strong);
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___297_8808.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___297_8808.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let stack' =
                         let tail1 = (Cfg cfg) :: stack  in
                         if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           let uu____8815 =
                             let uu____8816 =
                               let uu____8821 = FStar_Util.now ()  in
                               (t1, uu____8821)  in
                             Debug uu____8816  in
                           uu____8815 :: tail1
                         else tail1  in
                       norm cfg'1 env stack' tm))))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____8825 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____8825
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____8834 =
                      let uu____8841 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____8841, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____8834  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____8850 = lookup_bvar env x  in
               (match uu____8850 with
                | Univ uu____8851 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                    then
                      let uu____8900 = FStar_ST.op_Bang r  in
                      (match uu____8900 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9018  ->
                                 let uu____9019 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____9020 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____9019
                                   uu____9020);
                            (let uu____9021 = maybe_weakly_reduced t'  in
                             if uu____9021
                             then
                               match stack with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____9022 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____9097)::uu____9098 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____9108,uu____9109))::stack_rest ->
                    (match c with
                     | Univ uu____9113 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____9122 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____9151  ->
                                    let uu____9152 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____9152);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____9186  ->
                                    let uu____9187 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____9187);
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
                       (fun uu____9255  ->
                          let uu____9256 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____9256);
                     norm cfg env stack1 t1)
                | (Match uu____9257)::uu____9258 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9271 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9271 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9307  -> dummy :: env1) env)
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
                                          let uu____9350 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9350)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___299_9357 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___299_9357.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___299_9357.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9358 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9364  ->
                                 let uu____9365 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9365);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___300_9376 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___300_9376.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___300_9376.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___300_9376.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___300_9376.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___300_9376.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___300_9376.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___300_9376.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___300_9376.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____9379)::uu____9380 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9389 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9389 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9425  -> dummy :: env1) env)
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
                                          let uu____9468 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9468)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___299_9475 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___299_9475.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___299_9475.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9476 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9482  ->
                                 let uu____9483 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9483);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___300_9494 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___300_9494.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___300_9494.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___300_9494.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___300_9494.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___300_9494.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___300_9494.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___300_9494.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___300_9494.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____9497)::uu____9498 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9509 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9509 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9545  -> dummy :: env1) env)
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
                                          let uu____9588 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9588)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___299_9595 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___299_9595.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___299_9595.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9596 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9602  ->
                                 let uu____9603 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9603);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___300_9614 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___300_9614.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___300_9614.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___300_9614.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___300_9614.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___300_9614.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___300_9614.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___300_9614.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___300_9614.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____9617)::uu____9618 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9631 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9631 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9667  -> dummy :: env1) env)
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
                                          let uu____9710 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9710)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___299_9717 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___299_9717.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___299_9717.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9718 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9724  ->
                                 let uu____9725 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9725);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___300_9736 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___300_9736.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___300_9736.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___300_9736.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___300_9736.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___300_9736.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___300_9736.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___300_9736.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___300_9736.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____9739)::uu____9740 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9753 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9753 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9789  -> dummy :: env1) env)
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
                                          let uu____9832 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9832)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___299_9839 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___299_9839.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___299_9839.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9840 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9846  ->
                                 let uu____9847 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9847);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___300_9858 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___300_9858.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___300_9858.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___300_9858.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___300_9858.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___300_9858.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___300_9858.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___300_9858.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___300_9858.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____9861)::uu____9862 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9879 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9879 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9915  -> dummy :: env1) env)
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
                                          let uu____9958 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9958)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___299_9965 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___299_9965.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___299_9965.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9966 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9972  ->
                                 let uu____9973 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9973);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___300_9984 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___300_9984.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___300_9984.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___300_9984.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___300_9984.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___300_9984.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___300_9984.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___300_9984.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___300_9984.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____9989 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9989 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10025  -> dummy :: env1) env)
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
                                          let uu____10068 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10068)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___299_10075 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___299_10075.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___299_10075.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10076 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10082  ->
                                 let uu____10083 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10083);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___300_10094 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___300_10094.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___300_10094.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___300_10094.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___300_10094.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___300_10094.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___300_10094.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___300_10094.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___300_10094.FStar_TypeChecker_Cfg.reifying)
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
                      (fun uu____10137  ->
                         fun stack1  ->
                           match uu____10137 with
                           | (a,aq) ->
                               let uu____10149 =
                                 let uu____10150 =
                                   let uu____10157 =
                                     let uu____10158 =
                                       let uu____10189 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____10189, false)  in
                                     Clos uu____10158  in
                                   (uu____10157, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____10150  in
                               uu____10149 :: stack1) args)
                  in
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____10277  ->
                     let uu____10278 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____10278);
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
                             ((let uu___301_10326 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___301_10326.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___301_10326.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____10327 ->
                      let uu____10342 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10342)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____10345 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____10345 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____10376 =
                          let uu____10377 =
                            let uu____10384 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___302_10390 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___302_10390.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___302_10390.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____10384)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____10377  in
                        mk uu____10376 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____10413 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____10413
               else
                 (let uu____10415 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____10415 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____10423 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____10449  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____10423 c1  in
                      let t2 =
                        let uu____10473 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____10473 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____10586)::uu____10587 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10600  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____10601)::uu____10602 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10613  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____10614,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____10615;
                                   FStar_Syntax_Syntax.vars = uu____10616;_},uu____10617,uu____10618))::uu____10619
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10626  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____10627)::uu____10628 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10639  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____10640 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10643  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____10647  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____10672 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____10672
                         | FStar_Util.Inr c ->
                             let uu____10686 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____10686
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____10709 =
                               let uu____10710 =
                                 let uu____10737 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____10737, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____10710
                                in
                             mk uu____10709 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____10772 ->
                           let uu____10773 =
                             let uu____10774 =
                               let uu____10775 =
                                 let uu____10802 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____10802, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____10775
                                in
                             mk uu____10774 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____10773))))
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
                   let uu___303_10879 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___304_10882 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___304_10882.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___304_10882.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___304_10882.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___304_10882.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___304_10882.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___304_10882.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___304_10882.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___304_10882.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___304_10882.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___304_10882.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___304_10882.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___304_10882.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___304_10882.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___304_10882.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___304_10882.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___304_10882.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___304_10882.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___304_10882.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___304_10882.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___304_10882.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___304_10882.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___304_10882.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___304_10882.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___304_10882.FStar_TypeChecker_Cfg.nbe_step)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___303_10879.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___303_10879.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___303_10879.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___303_10879.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___303_10879.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___303_10879.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___303_10879.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___303_10879.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____10918 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____10918 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___305_10938 = cfg  in
                               let uu____10939 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___305_10938.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____10939;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___305_10938.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___305_10938.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___305_10938.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___305_10938.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___305_10938.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___305_10938.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___305_10938.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____10946 =
                                 let uu____10947 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____10947  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____10946
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___306_10950 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___306_10950.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___306_10950.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___306_10950.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___306_10950.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____10951 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____10951
           | FStar_Syntax_Syntax.Tm_let
               ((uu____10962,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____10963;
                               FStar_Syntax_Syntax.lbunivs = uu____10964;
                               FStar_Syntax_Syntax.lbtyp = uu____10965;
                               FStar_Syntax_Syntax.lbeff = uu____10966;
                               FStar_Syntax_Syntax.lbdef = uu____10967;
                               FStar_Syntax_Syntax.lbattrs = uu____10968;
                               FStar_Syntax_Syntax.lbpos = uu____10969;_}::uu____10970),uu____10971)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name
                   cfg.FStar_TypeChecker_Cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____11011 =
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
               if uu____11011
               then
                 let binder =
                   let uu____11013 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____11013  in
                 let env1 =
                   let uu____11023 =
                     let uu____11030 =
                       let uu____11031 =
                         let uu____11062 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____11062,
                           false)
                          in
                       Clos uu____11031  in
                     ((FStar_Pervasives_Native.Some binder), uu____11030)  in
                   uu____11023 :: env  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____11157  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                 then
                   (FStar_TypeChecker_Cfg.log cfg
                      (fun uu____11161  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____11162 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____11162))
                 else
                   (let uu____11164 =
                      let uu____11169 =
                        let uu____11170 =
                          let uu____11177 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____11177
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____11170]  in
                      FStar_Syntax_Subst.open_term uu____11169 body  in
                    match uu____11164 with
                    | (bs,body1) ->
                        (FStar_TypeChecker_Cfg.log cfg
                           (fun uu____11204  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____11212 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____11212  in
                            FStar_Util.Inl
                              (let uu___307_11228 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___307_11228.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___307_11228.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____11231  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___308_11233 = lb  in
                             let uu____11234 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___308_11233.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___308_11233.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____11234;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___308_11233.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___308_11233.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11263  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___309_11288 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps =
                                 (uu___309_11288.FStar_TypeChecker_Cfg.steps);
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___309_11288.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___309_11288.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 (uu___309_11288.FStar_TypeChecker_Cfg.delta_level);
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___309_11288.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong = true;
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___309_11288.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___309_11288.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___309_11288.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           FStar_TypeChecker_Cfg.log cfg1
                             (fun uu____11291  ->
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
               let uu____11308 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____11308 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____11344 =
                               let uu___310_11345 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___310_11345.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___310_11345.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____11344  in
                           let uu____11346 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____11346 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____11372 =
                                   FStar_List.map (fun uu____11388  -> dummy)
                                     lbs1
                                    in
                                 let uu____11389 =
                                   let uu____11398 =
                                     FStar_List.map
                                       (fun uu____11420  -> dummy) xs1
                                      in
                                   FStar_List.append uu____11398 env  in
                                 FStar_List.append uu____11372 uu____11389
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____11446 =
                                       let uu___311_11447 = rc  in
                                       let uu____11448 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___311_11447.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____11448;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___311_11447.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____11446
                                 | uu____11457 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___312_11463 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___312_11463.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___312_11463.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___312_11463.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___312_11463.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____11473 =
                        FStar_List.map (fun uu____11489  -> dummy) lbs2  in
                      FStar_List.append uu____11473 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____11497 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____11497 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___313_11513 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___313_11513.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___313_11513.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
               ->
               let uu____11542 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____11542
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____11561 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____11637  ->
                        match uu____11637 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___314_11758 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___314_11758.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___314_11758.FStar_Syntax_Syntax.sort)
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
               (match uu____11561 with
                | (rec_env,memos,uu____11985) ->
                    let uu____12038 =
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
                             let uu____12349 =
                               let uu____12356 =
                                 let uu____12357 =
                                   let uu____12388 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____12388, false)
                                    in
                                 Clos uu____12357  in
                               (FStar_Pervasives_Native.None, uu____12356)
                                in
                             uu____12349 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____12492  ->
                     let uu____12493 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____12493);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____12515 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____12517::uu____12518 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____12523) ->
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
                             | uu____12550 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____12566 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____12566
                              | uu____12579 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____12585 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____12609 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____12623 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____12636 =
                        let uu____12637 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____12638 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____12637 uu____12638
                         in
                      failwith uu____12636
                    else
                      (let uu____12640 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____12640)
                | uu____12641 -> norm cfg env stack t2))

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
              let uu____12650 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____12650 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____12664  ->
                        let uu____12665 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____12665);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____12676  ->
                        let uu____12677 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____12678 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____12677 uu____12678);
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
                      | (UnivArgs (us',uu____12691))::stack1 ->
                          ((let uu____12700 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____12700
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____12704 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____12704) us'
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
                      | uu____12737 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____12740 ->
                          let uu____12743 =
                            let uu____12744 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____12744
                             in
                          failwith uu____12743
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
                  let uu___315_12768 = cfg  in
                  let uu____12769 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____12769;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___315_12768.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___315_12768.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___315_12768.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___315_12768.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___315_12768.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___315_12768.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___315_12768.FStar_TypeChecker_Cfg.reifying)
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
                  (fun uu____12804  ->
                     let uu____12805 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____12806 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____12805
                       uu____12806);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____12808 =
                   let uu____12809 = FStar_Syntax_Subst.compress head3  in
                   uu____12809.FStar_Syntax_Syntax.n  in
                 match uu____12808 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____12827 =
                         FStar_TypeChecker_Env.norm_eff_name
                           cfg.FStar_TypeChecker_Cfg.tcenv m
                          in
                       FStar_TypeChecker_Env.get_effect_decl
                         cfg.FStar_TypeChecker_Cfg.tcenv uu____12827
                        in
                     let uu____12828 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____12828 with
                      | (uu____12829,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____12839 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____12849 =
                                   let uu____12850 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____12850.FStar_Syntax_Syntax.n  in
                                 match uu____12849 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____12856,uu____12857))
                                     ->
                                     let uu____12866 =
                                       let uu____12867 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____12867.FStar_Syntax_Syntax.n  in
                                     (match uu____12866 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____12873,msrc,uu____12875))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____12884 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____12884
                                      | uu____12885 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____12886 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____12887 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____12887 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___316_12892 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___316_12892.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___316_12892.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___316_12892.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___316_12892.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___316_12892.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____12893 = FStar_List.tl stack  in
                                    let uu____12894 =
                                      let uu____12895 =
                                        let uu____12902 =
                                          let uu____12903 =
                                            let uu____12916 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____12916)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____12903
                                           in
                                        FStar_Syntax_Syntax.mk uu____12902
                                         in
                                      uu____12895
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____12893 uu____12894
                                | FStar_Pervasives_Native.None  ->
                                    let uu____12932 =
                                      let uu____12933 = is_return body  in
                                      match uu____12933 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____12937;
                                            FStar_Syntax_Syntax.vars =
                                              uu____12938;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____12941 -> false  in
                                    if uu____12932
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
                                         let uu____12962 =
                                           let uu____12969 =
                                             let uu____12970 =
                                               let uu____12989 =
                                                 let uu____12998 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____12998]  in
                                               (uu____12989, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____12970
                                              in
                                           FStar_Syntax_Syntax.mk uu____12969
                                            in
                                         uu____12962
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____13040 =
                                           let uu____13041 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____13041.FStar_Syntax_Syntax.n
                                            in
                                         match uu____13040 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____13047::uu____13048::[])
                                             ->
                                             let uu____13053 =
                                               let uu____13060 =
                                                 let uu____13061 =
                                                   let uu____13068 =
                                                     let uu____13069 =
                                                       let uu____13070 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.FStar_TypeChecker_Cfg.tcenv
                                                         uu____13070
                                                        in
                                                     let uu____13071 =
                                                       let uu____13074 =
                                                         let uu____13075 =
                                                           close1 t  in
                                                         (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.FStar_TypeChecker_Cfg.tcenv
                                                           uu____13075
                                                          in
                                                       [uu____13074]  in
                                                     uu____13069 ::
                                                       uu____13071
                                                      in
                                                   (bind1, uu____13068)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____13061
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____13060
                                                in
                                             uu____13053
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____13081 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____13095 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____13095
                                         then
                                           let uu____13106 =
                                             let uu____13115 =
                                               FStar_TypeChecker_Cfg.embed_simple
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____13115
                                              in
                                           let uu____13116 =
                                             let uu____13127 =
                                               let uu____13136 =
                                                 FStar_TypeChecker_Cfg.embed_simple
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____13136
                                                in
                                             [uu____13127]  in
                                           uu____13106 :: uu____13116
                                         else []  in
                                       let reified =
                                         let uu____13173 =
                                           let uu____13180 =
                                             let uu____13181 =
                                               let uu____13198 =
                                                 let uu____13209 =
                                                   let uu____13220 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____13229 =
                                                     let uu____13240 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____13240]  in
                                                   uu____13220 :: uu____13229
                                                    in
                                                 let uu____13273 =
                                                   let uu____13284 =
                                                     let uu____13295 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____13304 =
                                                       let uu____13315 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____13324 =
                                                         let uu____13335 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____13344 =
                                                           let uu____13355 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____13355]  in
                                                         uu____13335 ::
                                                           uu____13344
                                                          in
                                                       uu____13315 ::
                                                         uu____13324
                                                        in
                                                     uu____13295 ::
                                                       uu____13304
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____13284
                                                    in
                                                 FStar_List.append
                                                   uu____13209 uu____13273
                                                  in
                                               (bind_inst, uu____13198)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____13181
                                              in
                                           FStar_Syntax_Syntax.mk uu____13180
                                            in
                                         uu____13173
                                           FStar_Pervasives_Native.None rng
                                          in
                                       FStar_TypeChecker_Cfg.log cfg
                                         (fun uu____13439  ->
                                            let uu____13440 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____13441 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____13440 uu____13441);
                                       (let uu____13442 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____13442 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let maybe_unfold_action head4 =
                       let maybe_extract_fv t1 =
                         let t2 =
                           let uu____13496 =
                             let uu____13497 = FStar_Syntax_Subst.compress t1
                                in
                             uu____13497.FStar_Syntax_Syntax.n  in
                           match uu____13496 with
                           | FStar_Syntax_Syntax.Tm_uinst (t2,uu____13501) ->
                               t2
                           | uu____13506 -> head4  in
                         let uu____13507 =
                           let uu____13508 = FStar_Syntax_Subst.compress t2
                              in
                           uu____13508.FStar_Syntax_Syntax.n  in
                         match uu____13507 with
                         | FStar_Syntax_Syntax.Tm_fvar x ->
                             FStar_Pervasives_Native.Some x
                         | uu____13514 -> FStar_Pervasives_Native.None  in
                       let uu____13515 = maybe_extract_fv head4  in
                       match uu____13515 with
                       | FStar_Pervasives_Native.Some x when
                           let uu____13525 = FStar_Syntax_Syntax.lid_of_fv x
                              in
                           FStar_TypeChecker_Env.is_action
                             cfg.FStar_TypeChecker_Cfg.tcenv uu____13525
                           ->
                           let head5 = norm cfg env [] head4  in
                           let action_unfolded =
                             let uu____13530 = maybe_extract_fv head5  in
                             match uu____13530 with
                             | FStar_Pervasives_Native.Some uu____13535 ->
                                 FStar_Pervasives_Native.Some true
                             | uu____13536 ->
                                 FStar_Pervasives_Native.Some false
                              in
                           (head5, action_unfolded)
                       | uu____13541 -> (head4, FStar_Pervasives_Native.None)
                        in
                     ((let uu____13547 = FStar_Options.defensive ()  in
                       if uu____13547
                       then
                         let is_arg_impure uu____13559 =
                           match uu____13559 with
                           | (e,q) ->
                               let uu____13572 =
                                 let uu____13573 =
                                   FStar_Syntax_Subst.compress e  in
                                 uu____13573.FStar_Syntax_Syntax.n  in
                               (match uu____13572 with
                                | FStar_Syntax_Syntax.Tm_meta
                                    (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                     (m1,m2,t'))
                                    ->
                                    let uu____13588 =
                                      FStar_Syntax_Util.is_pure_effect m1  in
                                    Prims.op_Negation uu____13588
                                | uu____13589 -> false)
                            in
                         let uu____13590 =
                           let uu____13591 =
                             let uu____13602 =
                               FStar_Syntax_Syntax.as_arg head_app  in
                             uu____13602 :: args  in
                           FStar_Util.for_some is_arg_impure uu____13591  in
                         (if uu____13590
                          then
                            let uu____13627 =
                              let uu____13632 =
                                let uu____13633 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____13633
                                 in
                              (FStar_Errors.Warning_Defensive, uu____13632)
                               in
                            FStar_Errors.log_issue
                              head3.FStar_Syntax_Syntax.pos uu____13627
                          else ())
                       else ());
                      (let uu____13636 = maybe_unfold_action head_app  in
                       match uu____13636 with
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
                              (fun uu____13681  ->
                                 let uu____13682 =
                                   FStar_Syntax_Print.term_to_string head0
                                    in
                                 let uu____13683 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                   uu____13682 uu____13683);
                            (let uu____13684 = FStar_List.tl stack  in
                             norm cfg env uu____13684 body1))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____13686) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____13710 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____13710  in
                     (FStar_TypeChecker_Cfg.log cfg
                        (fun uu____13714  ->
                           let uu____13715 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____13715);
                      (let uu____13716 = FStar_List.tl stack  in
                       norm cfg env uu____13716 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____13837  ->
                               match uu____13837 with
                               | (pat,wopt,tm) ->
                                   let uu____13885 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____13885)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____13917 = FStar_List.tl stack  in
                     norm cfg env uu____13917 tm
                 | uu____13918 -> fallback ())

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
              (fun uu____13932  ->
                 let uu____13933 = FStar_Ident.string_of_lid msrc  in
                 let uu____13934 = FStar_Ident.string_of_lid mtgt  in
                 let uu____13935 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____13933
                   uu____13934 uu____13935);
            (let uu____13936 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____13936
             then
               let ed =
                 let uu____13938 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____13938  in
               let uu____13939 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____13939 with
               | (uu____13940,return_repr) ->
                   let return_inst =
                     let uu____13953 =
                       let uu____13954 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____13954.FStar_Syntax_Syntax.n  in
                     match uu____13953 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____13960::[]) ->
                         let uu____13965 =
                           let uu____13972 =
                             let uu____13973 =
                               let uu____13980 =
                                 let uu____13981 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____13981]  in
                               (return_tm, uu____13980)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____13973  in
                           FStar_Syntax_Syntax.mk uu____13972  in
                         uu____13965 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____13987 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____13990 =
                     let uu____13997 =
                       let uu____13998 =
                         let uu____14015 =
                           let uu____14026 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____14035 =
                             let uu____14046 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____14046]  in
                           uu____14026 :: uu____14035  in
                         (return_inst, uu____14015)  in
                       FStar_Syntax_Syntax.Tm_app uu____13998  in
                     FStar_Syntax_Syntax.mk uu____13997  in
                   uu____13990 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____14095 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____14095 with
                | FStar_Pervasives_Native.None  ->
                    let uu____14098 =
                      let uu____14099 = FStar_Ident.text_of_lid msrc  in
                      let uu____14100 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____14099 uu____14100
                       in
                    failwith uu____14098
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14101;
                      FStar_TypeChecker_Env.mtarget = uu____14102;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14103;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____14125 =
                      let uu____14126 = FStar_Ident.text_of_lid msrc  in
                      let uu____14127 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____14126 uu____14127
                       in
                    failwith uu____14125
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14128;
                      FStar_TypeChecker_Env.mtarget = uu____14129;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14130;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____14165 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____14166 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____14165 t FStar_Syntax_Syntax.tun uu____14166))

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
                (fun uu____14236  ->
                   match uu____14236 with
                   | (a,imp) ->
                       let uu____14255 = norm cfg env [] a  in
                       (uu____14255, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____14265  ->
             let uu____14266 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____14267 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____14266 uu____14267);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____14291 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____14291
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___317_14294 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___317_14294.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___317_14294.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____14316 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____14316
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___318_14319 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___318_14319.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___318_14319.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____14364  ->
                      match uu____14364 with
                      | (a,i) ->
                          let uu____14383 = norm cfg env [] a  in
                          (uu____14383, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___262_14405  ->
                       match uu___262_14405 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____14409 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____14409
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___319_14417 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___320_14420 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___320_14420.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___319_14417.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___319_14417.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun uu____14423  ->
        match uu____14423 with
        | (x,imp) ->
            let uu____14430 =
              let uu___321_14431 = x  in
              let uu____14432 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___321_14431.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___321_14431.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____14432
              }  in
            (uu____14430, imp)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____14440 =
          FStar_List.fold_left
            (fun uu____14474  ->
               fun b  ->
                 match uu____14474 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____14440 with | (nbs,uu____14554) -> FStar_List.rev nbs

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
            let uu____14586 =
              let uu___322_14587 = rc  in
              let uu____14588 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___322_14587.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____14588;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___322_14587.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____14586
        | uu____14597 -> lopt

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
            (let uu____14606 = FStar_Syntax_Print.term_to_string tm  in
             let uu____14607 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____14606 uu____14607)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___263_14611  ->
      match uu___263_14611 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____14624 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____14624 with
           | FStar_Pervasives_Native.Some (t,uu____14632) -> t
           | FStar_Pervasives_Native.None  ->
               let uu____14641 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____14641)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____14649 = norm_cb cfg  in
            reduce_primops uu____14649 cfg env tm  in
          let uu____14656 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____14656
          then tm1
          else
            (let w t =
               let uu___323_14670 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___323_14670.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___323_14670.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____14681 =
                 let uu____14682 = FStar_Syntax_Util.unmeta t  in
                 uu____14682.FStar_Syntax_Syntax.n  in
               match uu____14681 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____14689 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____14750)::args1,(bv,uu____14753)::bs1) ->
                   let uu____14807 =
                     let uu____14808 = FStar_Syntax_Subst.compress t  in
                     uu____14808.FStar_Syntax_Syntax.n  in
                   (match uu____14807 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____14812 -> false)
               | ([],[]) -> true
               | (uu____14841,uu____14842) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____14891 = FStar_Syntax_Print.term_to_string t  in
                  let uu____14892 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____14891
                    uu____14892)
               else ();
               (let uu____14894 = FStar_Syntax_Util.head_and_args' t  in
                match uu____14894 with
                | (hd1,args) ->
                    let uu____14933 =
                      let uu____14934 = FStar_Syntax_Subst.compress hd1  in
                      uu____14934.FStar_Syntax_Syntax.n  in
                    (match uu____14933 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____14941 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____14942 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____14943 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____14941 uu____14942 uu____14943)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____14945 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____14962 = FStar_Syntax_Print.term_to_string t  in
                  let uu____14963 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____14962
                    uu____14963)
               else ();
               (let uu____14965 = FStar_Syntax_Util.is_squash t  in
                match uu____14965 with
                | FStar_Pervasives_Native.Some (uu____14976,t') ->
                    is_applied bs t'
                | uu____14988 ->
                    let uu____14997 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____14997 with
                     | FStar_Pervasives_Native.Some (uu____15008,t') ->
                         is_applied bs t'
                     | uu____15020 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____15044 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____15044 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____15051)::(q,uu____15053)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____15095 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____15096 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____15095 uu____15096)
                    else ();
                    (let uu____15098 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____15098 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____15103 =
                           let uu____15104 = FStar_Syntax_Subst.compress p
                              in
                           uu____15104.FStar_Syntax_Syntax.n  in
                         (match uu____15103 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____15112 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____15112))
                          | uu____15115 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____15118)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____15143 =
                           let uu____15144 = FStar_Syntax_Subst.compress p1
                              in
                           uu____15144.FStar_Syntax_Syntax.n  in
                         (match uu____15143 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____15152 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____15152))
                          | uu____15155 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____15159 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____15159 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____15164 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____15164 with
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
                                     let uu____15175 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____15175))
                               | uu____15178 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____15183)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____15208 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____15208 with
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
                                     let uu____15219 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____15219))
                               | uu____15222 -> FStar_Pervasives_Native.None)
                          | uu____15225 -> FStar_Pervasives_Native.None)
                     | uu____15228 -> FStar_Pervasives_Native.None))
               | uu____15231 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____15244 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____15244 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____15250)::[],uu____15251,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____15270 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____15271 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____15270
                         uu____15271)
                    else ();
                    is_quantified_const bv phi')
               | uu____15273 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____15286 =
                 let uu____15287 = FStar_Syntax_Subst.compress phi  in
                 uu____15287.FStar_Syntax_Syntax.n  in
               match uu____15286 with
               | FStar_Syntax_Syntax.Tm_match (uu____15292,br::brs) ->
                   let uu____15359 = br  in
                   (match uu____15359 with
                    | (uu____15376,uu____15377,e) ->
                        let r =
                          let uu____15398 = simp_t e  in
                          match uu____15398 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____15404 =
                                FStar_List.for_all
                                  (fun uu____15422  ->
                                     match uu____15422 with
                                     | (uu____15435,uu____15436,e') ->
                                         let uu____15450 = simp_t e'  in
                                         uu____15450 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____15404
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____15458 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____15467 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____15467
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____15502 =
                 match uu____15502 with
                 | (t1,q) ->
                     let uu____15523 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____15523 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____15555 -> (t1, q))
                  in
               let uu____15568 = FStar_Syntax_Util.head_and_args t  in
               match uu____15568 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____15646 =
                 let uu____15647 = FStar_Syntax_Util.unmeta ty  in
                 uu____15647.FStar_Syntax_Syntax.n  in
               match uu____15646 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____15651) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____15656,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____15680 -> false  in
             let simplify1 arg =
               let uu____15711 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____15711, arg)  in
             let uu____15724 = is_forall_const tm1  in
             match uu____15724 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____15729 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____15730 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____15729
                       uu____15730)
                  else ();
                  (let uu____15732 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____15732))
             | FStar_Pervasives_Native.None  ->
                 let uu____15733 =
                   let uu____15734 = FStar_Syntax_Subst.compress tm1  in
                   uu____15734.FStar_Syntax_Syntax.n  in
                 (match uu____15733 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____15738;
                              FStar_Syntax_Syntax.vars = uu____15739;_},uu____15740);
                         FStar_Syntax_Syntax.pos = uu____15741;
                         FStar_Syntax_Syntax.vars = uu____15742;_},args)
                      ->
                      let uu____15772 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____15772
                      then
                        let uu____15773 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____15773 with
                         | (FStar_Pervasives_Native.Some (true ),uu____15828)::
                             (uu____15829,(arg,uu____15831))::[] ->
                             maybe_auto_squash arg
                         | (uu____15896,(arg,uu____15898))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____15899)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____15964)::uu____15965::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____16028::(FStar_Pervasives_Native.Some (false
                                         ),uu____16029)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____16092 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____16108 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____16108
                         then
                           let uu____16109 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____16109 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____16164)::uu____16165::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____16228::(FStar_Pervasives_Native.Some (true
                                           ),uu____16229)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____16292)::(uu____16293,(arg,uu____16295))::[]
                               -> maybe_auto_squash arg
                           | (uu____16360,(arg,uu____16362))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____16363)::[]
                               -> maybe_auto_squash arg
                           | uu____16428 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____16444 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____16444
                            then
                              let uu____16445 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____16445 with
                              | uu____16500::(FStar_Pervasives_Native.Some
                                              (true ),uu____16501)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____16564)::uu____16565::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____16628)::(uu____16629,(arg,uu____16631))::[]
                                  -> maybe_auto_squash arg
                              | (uu____16696,(p,uu____16698))::(uu____16699,
                                                                (q,uu____16701))::[]
                                  ->
                                  let uu____16766 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____16766
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____16768 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____16784 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____16784
                               then
                                 let uu____16785 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____16785 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16840)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____16841)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____16906)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____16907)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16972)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____16973)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17038)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17039)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____17104,(arg,uu____17106))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____17107)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17172)::(uu____17173,(arg,uu____17175))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____17240,(arg,uu____17242))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____17243)::[]
                                     ->
                                     let uu____17308 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17308
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17309)::(uu____17310,(arg,uu____17312))::[]
                                     ->
                                     let uu____17377 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17377
                                 | (uu____17378,(p,uu____17380))::(uu____17381,
                                                                   (q,uu____17383))::[]
                                     ->
                                     let uu____17448 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____17448
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____17450 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____17466 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____17466
                                  then
                                    let uu____17467 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____17467 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____17522)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____17561)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____17600 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____17616 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____17616
                                     then
                                       match args with
                                       | (t,uu____17618)::[] ->
                                           let uu____17643 =
                                             let uu____17644 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17644.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17643 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17647::[],body,uu____17649)
                                                ->
                                                let uu____17684 = simp_t body
                                                   in
                                                (match uu____17684 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____17687 -> tm1)
                                            | uu____17690 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____17692))::(t,uu____17694)::[]
                                           ->
                                           let uu____17733 =
                                             let uu____17734 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17734.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17733 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17737::[],body,uu____17739)
                                                ->
                                                let uu____17774 = simp_t body
                                                   in
                                                (match uu____17774 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____17777 -> tm1)
                                            | uu____17780 -> tm1)
                                       | uu____17781 -> tm1
                                     else
                                       (let uu____17793 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____17793
                                        then
                                          match args with
                                          | (t,uu____17795)::[] ->
                                              let uu____17820 =
                                                let uu____17821 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17821.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17820 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17824::[],body,uu____17826)
                                                   ->
                                                   let uu____17861 =
                                                     simp_t body  in
                                                   (match uu____17861 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____17864 -> tm1)
                                               | uu____17867 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____17869))::(t,uu____17871)::[]
                                              ->
                                              let uu____17910 =
                                                let uu____17911 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17911.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17910 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17914::[],body,uu____17916)
                                                   ->
                                                   let uu____17951 =
                                                     simp_t body  in
                                                   (match uu____17951 with
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
                                                    | uu____17954 -> tm1)
                                               | uu____17957 -> tm1)
                                          | uu____17958 -> tm1
                                        else
                                          (let uu____17970 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____17970
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____17971;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____17972;_},uu____17973)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____17998;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____17999;_},uu____18000)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____18025 -> tm1
                                           else
                                             (let uu____18037 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____18037 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____18057 ->
                                                  let uu____18066 =
                                                    let uu____18073 =
                                                      norm_cb cfg  in
                                                    reduce_equality
                                                      uu____18073 cfg env
                                                     in
                                                  uu____18066 tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____18081;
                         FStar_Syntax_Syntax.vars = uu____18082;_},args)
                      ->
                      let uu____18108 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18108
                      then
                        let uu____18109 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18109 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18164)::
                             (uu____18165,(arg,uu____18167))::[] ->
                             maybe_auto_squash arg
                         | (uu____18232,(arg,uu____18234))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18235)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18300)::uu____18301::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18364::(FStar_Pervasives_Native.Some (false
                                         ),uu____18365)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18428 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18444 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18444
                         then
                           let uu____18445 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18445 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18500)::uu____18501::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18564::(FStar_Pervasives_Native.Some (true
                                           ),uu____18565)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18628)::(uu____18629,(arg,uu____18631))::[]
                               -> maybe_auto_squash arg
                           | (uu____18696,(arg,uu____18698))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18699)::[]
                               -> maybe_auto_squash arg
                           | uu____18764 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18780 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____18780
                            then
                              let uu____18781 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____18781 with
                              | uu____18836::(FStar_Pervasives_Native.Some
                                              (true ),uu____18837)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____18900)::uu____18901::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____18964)::(uu____18965,(arg,uu____18967))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19032,(p,uu____19034))::(uu____19035,
                                                                (q,uu____19037))::[]
                                  ->
                                  let uu____19102 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19102
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19104 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19120 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19120
                               then
                                 let uu____19121 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19121 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19176)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19177)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19242)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19243)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19308)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19309)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19374)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19375)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19440,(arg,uu____19442))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19443)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19508)::(uu____19509,(arg,uu____19511))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19576,(arg,uu____19578))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19579)::[]
                                     ->
                                     let uu____19644 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19644
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19645)::(uu____19646,(arg,uu____19648))::[]
                                     ->
                                     let uu____19713 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19713
                                 | (uu____19714,(p,uu____19716))::(uu____19717,
                                                                   (q,uu____19719))::[]
                                     ->
                                     let uu____19784 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19784
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19786 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19802 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19802
                                  then
                                    let uu____19803 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19803 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19858)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19897)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19936 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19952 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19952
                                     then
                                       match args with
                                       | (t,uu____19954)::[] ->
                                           let uu____19979 =
                                             let uu____19980 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19980.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19979 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19983::[],body,uu____19985)
                                                ->
                                                let uu____20020 = simp_t body
                                                   in
                                                (match uu____20020 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20023 -> tm1)
                                            | uu____20026 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20028))::(t,uu____20030)::[]
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
                                                 | uu____20113 -> tm1)
                                            | uu____20116 -> tm1)
                                       | uu____20117 -> tm1
                                     else
                                       (let uu____20129 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20129
                                        then
                                          match args with
                                          | (t,uu____20131)::[] ->
                                              let uu____20156 =
                                                let uu____20157 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20157.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20156 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20160::[],body,uu____20162)
                                                   ->
                                                   let uu____20197 =
                                                     simp_t body  in
                                                   (match uu____20197 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20200 -> tm1)
                                               | uu____20203 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20205))::(t,uu____20207)::[]
                                              ->
                                              let uu____20246 =
                                                let uu____20247 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20247.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20246 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20250::[],body,uu____20252)
                                                   ->
                                                   let uu____20287 =
                                                     simp_t body  in
                                                   (match uu____20287 with
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
                                                    | uu____20290 -> tm1)
                                               | uu____20293 -> tm1)
                                          | uu____20294 -> tm1
                                        else
                                          (let uu____20306 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20306
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20307;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20308;_},uu____20309)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20334;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20335;_},uu____20336)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20361 -> tm1
                                           else
                                             (let uu____20373 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20373 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20393 ->
                                                  let uu____20402 =
                                                    let uu____20409 =
                                                      norm_cb cfg  in
                                                    reduce_equality
                                                      uu____20409 cfg env
                                                     in
                                                  uu____20402 tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____20422 = simp_t t  in
                      (match uu____20422 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____20425 ->
                      let uu____20448 = is_const_match tm1  in
                      (match uu____20448 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____20451 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____20461  ->
               (let uu____20463 = FStar_Syntax_Print.tag_of_term t  in
                let uu____20464 = FStar_Syntax_Print.term_to_string t  in
                let uu____20465 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____20472 =
                  let uu____20473 =
                    let uu____20476 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____20476
                     in
                  stack_to_string uu____20473  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____20463 uu____20464 uu____20465 uu____20472);
               (let uu____20499 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____20499
                then
                  let uu____20500 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____20500 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____20507 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____20508 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____20509 =
                          let uu____20510 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____20510
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____20507
                          uu____20508 uu____20509);
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
                   let uu____20528 =
                     let uu____20529 =
                       let uu____20530 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____20530  in
                     FStar_Util.string_of_int uu____20529  in
                   let uu____20535 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____20536 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____20528 uu____20535 uu____20536)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____20542,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                FStar_TypeChecker_Cfg.log cfg
                  (fun uu____20593  ->
                     let uu____20594 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____20594);
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
               let uu____20632 =
                 let uu___324_20633 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___324_20633.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___324_20633.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____20632
           | (Arg (Univ uu____20636,uu____20637,uu____20638))::uu____20639 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____20642,uu____20643))::uu____20644 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____20659,uu____20660),aq,r))::stack1
               when
               let uu____20710 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____20710 ->
               let t2 =
                 let uu____20714 =
                   let uu____20719 =
                     let uu____20720 = closure_as_term cfg env_arg tm  in
                     (uu____20720, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____20719  in
                 uu____20714 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____20732),aq,r))::stack1 ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____20785  ->
                     let uu____20786 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____20786);
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
                  (let uu____20800 = FStar_ST.op_Bang m  in
                   match uu____20800 with
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
                   | FStar_Pervasives_Native.Some (uu____20941,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____20996 =
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____21000  ->
                      let uu____21001 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____21001);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____21009 =
                 let uu____21010 = FStar_Syntax_Subst.compress t1  in
                 uu____21010.FStar_Syntax_Syntax.n  in
               (match uu____21009 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____21037 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____21037  in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____21041  ->
                          let uu____21042 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____21042);
                     (let uu____21043 = FStar_List.tl stack  in
                      norm cfg env1 uu____21043 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____21044);
                       FStar_Syntax_Syntax.pos = uu____21045;
                       FStar_Syntax_Syntax.vars = uu____21046;_},(e,uu____21048)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____21087 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                    ->
                    let uu____21104 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____21104 with
                     | (hd1,args) ->
                         let uu____21147 =
                           let uu____21148 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____21148.FStar_Syntax_Syntax.n  in
                         (match uu____21147 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____21152 =
                                FStar_TypeChecker_Cfg.find_prim_step cfg fv
                                 in
                              (match uu____21152 with
                               | FStar_Pervasives_Native.Some
                                   {
                                     FStar_TypeChecker_Cfg.name = uu____21155;
                                     FStar_TypeChecker_Cfg.arity =
                                       uu____21156;
                                     FStar_TypeChecker_Cfg.univ_arity =
                                       uu____21157;
                                     FStar_TypeChecker_Cfg.auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     FStar_TypeChecker_Cfg.strong_reduction_ok
                                       = uu____21159;
                                     FStar_TypeChecker_Cfg.requires_binder_substitution
                                       = uu____21160;
                                     FStar_TypeChecker_Cfg.interpretation =
                                       uu____21161;
                                     FStar_TypeChecker_Cfg.interpretation_nbe
                                       = uu____21162;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____21196 -> fallback " (3)" ())
                          | uu____21199 -> fallback " (4)" ()))
                | uu____21200 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (FStar_TypeChecker_Cfg.log cfg1
                  (fun uu____21225  ->
                     let uu____21226 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____21226);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____21235 =
                   FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____21240  ->
                        let uu____21241 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____21242 =
                          let uu____21243 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____21270  ->
                                    match uu____21270 with
                                    | (p,uu____21280,uu____21281) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____21243
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____21241 uu____21242);
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
                             (fun uu___264_21298  ->
                                match uu___264_21298 with
                                | FStar_TypeChecker_Env.InliningDelta  ->
                                    true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____21299 -> false))
                         in
                      let steps =
                        let uu___325_21301 = cfg1.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___325_21301.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___325_21301.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta = false;
                          FStar_TypeChecker_Cfg.weak =
                            (uu___325_21301.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___325_21301.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___325_21301.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___325_21301.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___325_21301.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_tac = false;
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___325_21301.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___325_21301.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___325_21301.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___325_21301.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___325_21301.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___325_21301.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___325_21301.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___325_21301.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___325_21301.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___325_21301.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___325_21301.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___325_21301.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___325_21301.FStar_TypeChecker_Cfg.nbe_step)
                        }  in
                      let uu___326_21306 = cfg1  in
                      {
                        FStar_TypeChecker_Cfg.steps = steps;
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___326_21306.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___326_21306.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level = new_delta;
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___326_21306.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong = true;
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___326_21306.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___326_21306.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying =
                          (uu___326_21306.FStar_TypeChecker_Cfg.reifying)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____21378 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____21407 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____21491  ->
                                    fun uu____21492  ->
                                      match (uu____21491, uu____21492) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____21631 = norm_pat env3 p1
                                             in
                                          (match uu____21631 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____21407 with
                           | (pats1,env3) ->
                               ((let uu___327_21793 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___327_21793.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___328_21812 = x  in
                            let uu____21813 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___328_21812.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___328_21812.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21813
                            }  in
                          ((let uu___329_21827 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___329_21827.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___330_21838 = x  in
                            let uu____21839 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___330_21838.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___330_21838.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21839
                            }  in
                          ((let uu___331_21853 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___331_21853.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___332_21869 = x  in
                            let uu____21870 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___332_21869.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___332_21869.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21870
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___333_21885 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___333_21885.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____21929 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____21959 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____21959 with
                                  | (p,wopt,e) ->
                                      let uu____21979 = norm_pat env1 p  in
                                      (match uu____21979 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____22034 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____22034
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____22051 =
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
                      if uu____22051
                      then
                        norm
                          (let uu___334_22056 = cfg1  in
                           {
                             FStar_TypeChecker_Cfg.steps =
                               (let uu___335_22059 =
                                  cfg1.FStar_TypeChecker_Cfg.steps  in
                                {
                                  FStar_TypeChecker_Cfg.beta =
                                    (uu___335_22059.FStar_TypeChecker_Cfg.beta);
                                  FStar_TypeChecker_Cfg.iota =
                                    (uu___335_22059.FStar_TypeChecker_Cfg.iota);
                                  FStar_TypeChecker_Cfg.zeta =
                                    (uu___335_22059.FStar_TypeChecker_Cfg.zeta);
                                  FStar_TypeChecker_Cfg.weak =
                                    (uu___335_22059.FStar_TypeChecker_Cfg.weak);
                                  FStar_TypeChecker_Cfg.hnf =
                                    (uu___335_22059.FStar_TypeChecker_Cfg.hnf);
                                  FStar_TypeChecker_Cfg.primops =
                                    (uu___335_22059.FStar_TypeChecker_Cfg.primops);
                                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                    =
                                    (uu___335_22059.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                  FStar_TypeChecker_Cfg.unfold_until =
                                    (uu___335_22059.FStar_TypeChecker_Cfg.unfold_until);
                                  FStar_TypeChecker_Cfg.unfold_only =
                                    (uu___335_22059.FStar_TypeChecker_Cfg.unfold_only);
                                  FStar_TypeChecker_Cfg.unfold_fully =
                                    (uu___335_22059.FStar_TypeChecker_Cfg.unfold_fully);
                                  FStar_TypeChecker_Cfg.unfold_attr =
                                    (uu___335_22059.FStar_TypeChecker_Cfg.unfold_attr);
                                  FStar_TypeChecker_Cfg.unfold_tac =
                                    (uu___335_22059.FStar_TypeChecker_Cfg.unfold_tac);
                                  FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                    =
                                    (uu___335_22059.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                  FStar_TypeChecker_Cfg.simplify =
                                    (uu___335_22059.FStar_TypeChecker_Cfg.simplify);
                                  FStar_TypeChecker_Cfg.erase_universes =
                                    (uu___335_22059.FStar_TypeChecker_Cfg.erase_universes);
                                  FStar_TypeChecker_Cfg.allow_unbound_universes
                                    =
                                    (uu___335_22059.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                  FStar_TypeChecker_Cfg.reify_ =
                                    (uu___335_22059.FStar_TypeChecker_Cfg.reify_);
                                  FStar_TypeChecker_Cfg.compress_uvars =
                                    (uu___335_22059.FStar_TypeChecker_Cfg.compress_uvars);
                                  FStar_TypeChecker_Cfg.no_full_norm =
                                    (uu___335_22059.FStar_TypeChecker_Cfg.no_full_norm);
                                  FStar_TypeChecker_Cfg.check_no_uvars =
                                    (uu___335_22059.FStar_TypeChecker_Cfg.check_no_uvars);
                                  FStar_TypeChecker_Cfg.unmeta =
                                    (uu___335_22059.FStar_TypeChecker_Cfg.unmeta);
                                  FStar_TypeChecker_Cfg.unascribe =
                                    (uu___335_22059.FStar_TypeChecker_Cfg.unascribe);
                                  FStar_TypeChecker_Cfg.in_full_norm_request
                                    =
                                    (uu___335_22059.FStar_TypeChecker_Cfg.in_full_norm_request);
                                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                    = false;
                                  FStar_TypeChecker_Cfg.nbe_step =
                                    (uu___335_22059.FStar_TypeChecker_Cfg.nbe_step)
                                });
                             FStar_TypeChecker_Cfg.tcenv =
                               (uu___334_22056.FStar_TypeChecker_Cfg.tcenv);
                             FStar_TypeChecker_Cfg.debug =
                               (uu___334_22056.FStar_TypeChecker_Cfg.debug);
                             FStar_TypeChecker_Cfg.delta_level =
                               (uu___334_22056.FStar_TypeChecker_Cfg.delta_level);
                             FStar_TypeChecker_Cfg.primitive_steps =
                               (uu___334_22056.FStar_TypeChecker_Cfg.primitive_steps);
                             FStar_TypeChecker_Cfg.strong =
                               (uu___334_22056.FStar_TypeChecker_Cfg.strong);
                             FStar_TypeChecker_Cfg.memoize_lazy =
                               (uu___334_22056.FStar_TypeChecker_Cfg.memoize_lazy);
                             FStar_TypeChecker_Cfg.normalize_pure_lets =
                               (uu___334_22056.FStar_TypeChecker_Cfg.normalize_pure_lets);
                             FStar_TypeChecker_Cfg.reifying =
                               (uu___334_22056.FStar_TypeChecker_Cfg.reifying)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____22061 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____22061)
                    in
                 let rec is_cons head1 =
                   let uu____22086 =
                     let uu____22087 = FStar_Syntax_Subst.compress head1  in
                     uu____22087.FStar_Syntax_Syntax.n  in
                   match uu____22086 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____22091) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____22096 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____22097;
                         FStar_Syntax_Syntax.fv_delta = uu____22098;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____22099;
                         FStar_Syntax_Syntax.fv_delta = uu____22100;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____22101);_}
                       -> true
                   | uu____22108 -> false  in
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
                   let uu____22272 =
                     FStar_Syntax_Util.head_and_args scrutinee2  in
                   match uu____22272 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____22365 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee2.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____22404 ->
                                 let uu____22405 =
                                   let uu____22406 = is_cons head1  in
                                   Prims.op_Negation uu____22406  in
                                 FStar_Util.Inr uu____22405)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____22431 =
                              let uu____22432 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____22432.FStar_Syntax_Syntax.n  in
                            (match uu____22431 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____22450 ->
                                 let uu____22451 =
                                   let uu____22452 = is_cons head1  in
                                   Prims.op_Negation uu____22452  in
                                 FStar_Util.Inr uu____22451))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____22535)::rest_a,(p1,uu____22538)::rest_p) ->
                       let uu____22592 = matches_pat t2 p1  in
                       (match uu____22592 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____22641 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____22761 = matches_pat scrutinee1 p1  in
                       (match uu____22761 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (FStar_TypeChecker_Cfg.log cfg1
                               (fun uu____22801  ->
                                  let uu____22802 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____22803 =
                                    let uu____22804 =
                                      FStar_List.map
                                        (fun uu____22814  ->
                                           match uu____22814 with
                                           | (uu____22819,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____22804
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____22802 uu____22803);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____22851  ->
                                       match uu____22851 with
                                       | (bv,t2) ->
                                           let uu____22874 =
                                             let uu____22881 =
                                               let uu____22884 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____22884
                                                in
                                             let uu____22885 =
                                               let uu____22886 =
                                                 let uu____22917 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____22917, false)
                                                  in
                                               Clos uu____22886  in
                                             (uu____22881, uu____22885)  in
                                           uu____22874 :: env2) env1 s
                                 in
                              let uu____23030 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____23030)))
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
            (fun uu____23060  ->
               let uu____23061 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____23061);
          (let uu____23062 = is_nbe_request s  in
           if uu____23062
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____23066  ->
                   let uu____23067 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____23067);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____23071  ->
                   let uu____23072 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____23072);
              (let r = nbe_eval c s t  in
               FStar_TypeChecker_Cfg.log_top c
                 (fun uu____23077  ->
                    let uu____23078 = FStar_Syntax_Print.term_to_string r  in
                    FStar_Util.print1 "}\nNormalization result = (%s)\n"
                      uu____23078);
               r))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____23083  ->
                   let uu____23084 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____23084);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____23088  ->
                   let uu____23089 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____23089);
              (let r = norm c [] [] t  in
               FStar_TypeChecker_Cfg.log_top c
                 (fun uu____23100  ->
                    let uu____23101 = FStar_Syntax_Print.term_to_string r  in
                    FStar_Util.print1 "}\nNormalization result = (%s)\n"
                      uu____23101);
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
        let uu____23132 = FStar_TypeChecker_Cfg.config s e  in
        norm_comp uu____23132 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____23149 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____23149 [] u
  
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
        let uu____23173 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____23173  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____23180 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___336_23199 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___336_23199.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___336_23199.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name
              cfg.FStar_TypeChecker_Cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____23206 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____23206
          then
            let ct1 =
              let uu____23208 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____23208 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____23215 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____23215
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___337_23219 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___337_23219.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___337_23219.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___337_23219.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev
                      cfg.FStar_TypeChecker_Cfg.tcenv c
                     in
                  let uu___338_23221 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___338_23221.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___338_23221.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___338_23221.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___338_23221.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___339_23222 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___339_23222.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___339_23222.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____23224 -> c
  
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
        let uu____23242 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____23242  in
      let uu____23249 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____23249
      then
        let uu____23250 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____23250 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____23256  ->
                 let uu____23257 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____23257)
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
          (fun uu___341_23271  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___340_23274 ->
            ((let uu____23276 =
                let uu____23281 =
                  let uu____23282 = FStar_Util.message_of_exn uu___340_23274
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23282
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____23281)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____23276);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          (fun uu___343_23296  ->
             match () with
             | () ->
                 let uu____23297 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____23297 [] c) ()
        with
        | uu___342_23306 ->
            ((let uu____23308 =
                let uu____23313 =
                  let uu____23314 = FStar_Util.message_of_exn uu___342_23306
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23314
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____23313)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____23308);
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
                   let uu____23359 =
                     let uu____23360 =
                       let uu____23367 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____23367)  in
                     FStar_Syntax_Syntax.Tm_refine uu____23360  in
                   mk uu____23359 t01.FStar_Syntax_Syntax.pos
               | uu____23372 -> t2)
          | uu____23373 -> t2  in
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
        let uu____23452 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____23452 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____23489 ->
                 let uu____23498 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____23498 with
                  | (actuals,uu____23508,uu____23509) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____23527 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____23527 with
                         | (binders,args) ->
                             let uu____23538 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____23538
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
      | uu____23552 ->
          let uu____23553 = FStar_Syntax_Util.head_and_args t  in
          (match uu____23553 with
           | (head1,args) ->
               let uu____23596 =
                 let uu____23597 = FStar_Syntax_Subst.compress head1  in
                 uu____23597.FStar_Syntax_Syntax.n  in
               (match uu____23596 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____23618 =
                      let uu____23633 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____23633  in
                    (match uu____23618 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____23671 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___344_23679 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___344_23679.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___344_23679.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___344_23679.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___344_23679.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___344_23679.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___344_23679.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___344_23679.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___344_23679.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___344_23679.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___344_23679.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___344_23679.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___344_23679.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___344_23679.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___344_23679.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___344_23679.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___344_23679.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___344_23679.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___344_23679.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___344_23679.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___344_23679.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___344_23679.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___344_23679.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___344_23679.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___344_23679.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___344_23679.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___344_23679.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___344_23679.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___344_23679.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___344_23679.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___344_23679.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___344_23679.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___344_23679.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___344_23679.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___344_23679.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___344_23679.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___344_23679.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___344_23679.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___344_23679.FStar_TypeChecker_Env.dep_graph);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___344_23679.FStar_TypeChecker_Env.nbe)
                                 }) t
                               in
                            match uu____23671 with
                            | (uu____23680,ty,uu____23682) ->
                                eta_expand_with_type env t ty))
                | uu____23683 ->
                    let uu____23684 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___345_23692 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___345_23692.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___345_23692.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___345_23692.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___345_23692.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___345_23692.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___345_23692.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___345_23692.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___345_23692.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___345_23692.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___345_23692.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___345_23692.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___345_23692.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___345_23692.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___345_23692.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___345_23692.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___345_23692.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___345_23692.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___345_23692.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___345_23692.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___345_23692.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___345_23692.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___345_23692.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___345_23692.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___345_23692.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___345_23692.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___345_23692.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___345_23692.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___345_23692.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___345_23692.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___345_23692.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___345_23692.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___345_23692.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___345_23692.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___345_23692.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___345_23692.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___345_23692.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___345_23692.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___345_23692.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___345_23692.FStar_TypeChecker_Env.nbe)
                         }) t
                       in
                    (match uu____23684 with
                     | (uu____23693,ty,uu____23695) ->
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
      let uu___346_23776 = x  in
      let uu____23777 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___346_23776.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___346_23776.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____23777
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____23780 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____23803 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____23804 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____23805 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____23806 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____23813 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____23814 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____23815 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___347_23849 = rc  in
          let uu____23850 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____23859 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___347_23849.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____23850;
            FStar_Syntax_Syntax.residual_flags = uu____23859
          }  in
        let uu____23862 =
          let uu____23863 =
            let uu____23882 = elim_delayed_subst_binders bs  in
            let uu____23891 = elim_delayed_subst_term t2  in
            let uu____23894 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____23882, uu____23891, uu____23894)  in
          FStar_Syntax_Syntax.Tm_abs uu____23863  in
        mk1 uu____23862
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____23931 =
          let uu____23932 =
            let uu____23947 = elim_delayed_subst_binders bs  in
            let uu____23956 = elim_delayed_subst_comp c  in
            (uu____23947, uu____23956)  in
          FStar_Syntax_Syntax.Tm_arrow uu____23932  in
        mk1 uu____23931
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____23975 =
          let uu____23976 =
            let uu____23983 = elim_bv bv  in
            let uu____23984 = elim_delayed_subst_term phi  in
            (uu____23983, uu____23984)  in
          FStar_Syntax_Syntax.Tm_refine uu____23976  in
        mk1 uu____23975
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____24015 =
          let uu____24016 =
            let uu____24033 = elim_delayed_subst_term t2  in
            let uu____24036 = elim_delayed_subst_args args  in
            (uu____24033, uu____24036)  in
          FStar_Syntax_Syntax.Tm_app uu____24016  in
        mk1 uu____24015
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___348_24108 = p  in
              let uu____24109 =
                let uu____24110 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____24110  in
              {
                FStar_Syntax_Syntax.v = uu____24109;
                FStar_Syntax_Syntax.p =
                  (uu___348_24108.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___349_24112 = p  in
              let uu____24113 =
                let uu____24114 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____24114  in
              {
                FStar_Syntax_Syntax.v = uu____24113;
                FStar_Syntax_Syntax.p =
                  (uu___349_24112.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___350_24121 = p  in
              let uu____24122 =
                let uu____24123 =
                  let uu____24130 = elim_bv x  in
                  let uu____24131 = elim_delayed_subst_term t0  in
                  (uu____24130, uu____24131)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____24123  in
              {
                FStar_Syntax_Syntax.v = uu____24122;
                FStar_Syntax_Syntax.p =
                  (uu___350_24121.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___351_24154 = p  in
              let uu____24155 =
                let uu____24156 =
                  let uu____24169 =
                    FStar_List.map
                      (fun uu____24192  ->
                         match uu____24192 with
                         | (x,b) ->
                             let uu____24205 = elim_pat x  in
                             (uu____24205, b)) pats
                     in
                  (fv, uu____24169)  in
                FStar_Syntax_Syntax.Pat_cons uu____24156  in
              {
                FStar_Syntax_Syntax.v = uu____24155;
                FStar_Syntax_Syntax.p =
                  (uu___351_24154.FStar_Syntax_Syntax.p)
              }
          | uu____24218 -> p  in
        let elim_branch uu____24242 =
          match uu____24242 with
          | (pat,wopt,t3) ->
              let uu____24268 = elim_pat pat  in
              let uu____24271 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____24274 = elim_delayed_subst_term t3  in
              (uu____24268, uu____24271, uu____24274)
           in
        let uu____24279 =
          let uu____24280 =
            let uu____24303 = elim_delayed_subst_term t2  in
            let uu____24306 = FStar_List.map elim_branch branches  in
            (uu____24303, uu____24306)  in
          FStar_Syntax_Syntax.Tm_match uu____24280  in
        mk1 uu____24279
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____24437 =
          match uu____24437 with
          | (tc,topt) ->
              let uu____24472 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____24482 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____24482
                | FStar_Util.Inr c ->
                    let uu____24484 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____24484
                 in
              let uu____24485 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____24472, uu____24485)
           in
        let uu____24494 =
          let uu____24495 =
            let uu____24522 = elim_delayed_subst_term t2  in
            let uu____24525 = elim_ascription a  in
            (uu____24522, uu____24525, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____24495  in
        mk1 uu____24494
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___352_24586 = lb  in
          let uu____24587 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____24590 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___352_24586.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___352_24586.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____24587;
            FStar_Syntax_Syntax.lbeff =
              (uu___352_24586.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____24590;
            FStar_Syntax_Syntax.lbattrs =
              (uu___352_24586.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___352_24586.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____24593 =
          let uu____24594 =
            let uu____24607 =
              let uu____24614 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____24614)  in
            let uu____24623 = elim_delayed_subst_term t2  in
            (uu____24607, uu____24623)  in
          FStar_Syntax_Syntax.Tm_let uu____24594  in
        mk1 uu____24593
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____24667 =
          let uu____24668 =
            let uu____24675 = elim_delayed_subst_term tm  in
            (uu____24675, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____24668  in
        mk1 uu____24667
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____24686 =
          let uu____24687 =
            let uu____24694 = elim_delayed_subst_term t2  in
            let uu____24697 = elim_delayed_subst_meta md  in
            (uu____24694, uu____24697)  in
          FStar_Syntax_Syntax.Tm_meta uu____24687  in
        mk1 uu____24686

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___265_24706  ->
         match uu___265_24706 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____24710 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____24710
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
        let uu____24733 =
          let uu____24734 =
            let uu____24743 = elim_delayed_subst_term t  in
            (uu____24743, uopt)  in
          FStar_Syntax_Syntax.Total uu____24734  in
        mk1 uu____24733
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____24760 =
          let uu____24761 =
            let uu____24770 = elim_delayed_subst_term t  in
            (uu____24770, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____24761  in
        mk1 uu____24760
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___353_24779 = ct  in
          let uu____24780 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____24783 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____24794 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___353_24779.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___353_24779.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____24780;
            FStar_Syntax_Syntax.effect_args = uu____24783;
            FStar_Syntax_Syntax.flags = uu____24794
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___266_24797  ->
    match uu___266_24797 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____24811 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____24811
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____24850 =
          let uu____24857 = elim_delayed_subst_term t  in (m, uu____24857)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____24850
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____24869 =
          let uu____24878 = elim_delayed_subst_term t  in
          (m1, m2, uu____24878)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____24869
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
      (fun uu____24911  ->
         match uu____24911 with
         | (t,q) ->
             let uu____24930 = elim_delayed_subst_term t  in (uu____24930, q))
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
      (fun uu____24958  ->
         match uu____24958 with
         | (x,q) ->
             let uu____24977 =
               let uu___354_24978 = x  in
               let uu____24979 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___354_24978.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___354_24978.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____24979
               }  in
             (uu____24977, q)) bs

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
            | (uu____25085,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____25117,FStar_Util.Inl t) ->
                let uu____25139 =
                  let uu____25146 =
                    let uu____25147 =
                      let uu____25162 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____25162)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____25147  in
                  FStar_Syntax_Syntax.mk uu____25146  in
                uu____25139 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____25178 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____25178 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____25210 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____25283 ->
                    let uu____25284 =
                      let uu____25293 =
                        let uu____25294 = FStar_Syntax_Subst.compress t4  in
                        uu____25294.FStar_Syntax_Syntax.n  in
                      (uu____25293, tc)  in
                    (match uu____25284 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____25323) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____25370) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____25415,FStar_Util.Inl uu____25416) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____25447 -> failwith "Impossible")
                 in
              (match uu____25210 with
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
          let uu____25584 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____25584 with
          | (univ_names1,binders1,tc) ->
              let uu____25658 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____25658)
  
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
          let uu____25711 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____25711 with
          | (univ_names1,binders1,tc) ->
              let uu____25785 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____25785)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____25826 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____25826 with
           | (univ_names1,binders1,typ1) ->
               let uu___355_25866 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___355_25866.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___355_25866.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___355_25866.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___355_25866.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___356_25881 = s  in
          let uu____25882 =
            let uu____25883 =
              let uu____25892 = FStar_List.map (elim_uvars env) sigs  in
              (uu____25892, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____25883  in
          {
            FStar_Syntax_Syntax.sigel = uu____25882;
            FStar_Syntax_Syntax.sigrng =
              (uu___356_25881.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___356_25881.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___356_25881.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___356_25881.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____25909 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25909 with
           | (univ_names1,uu____25933,typ1) ->
               let uu___357_25955 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___357_25955.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___357_25955.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___357_25955.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___357_25955.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____25961 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25961 with
           | (univ_names1,uu____25985,typ1) ->
               let uu___358_26007 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___358_26007.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___358_26007.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___358_26007.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___358_26007.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____26035 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____26035 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____26060 =
                            let uu____26061 =
                              let uu____26062 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____26062  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____26061
                             in
                          elim_delayed_subst_term uu____26060  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___359_26065 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___359_26065.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___359_26065.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___359_26065.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___359_26065.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___360_26066 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___360_26066.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___360_26066.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___360_26066.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___360_26066.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___361_26072 = s  in
          let uu____26073 =
            let uu____26074 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____26074  in
          {
            FStar_Syntax_Syntax.sigel = uu____26073;
            FStar_Syntax_Syntax.sigrng =
              (uu___361_26072.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___361_26072.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___361_26072.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___361_26072.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____26078 = elim_uvars_aux_t env us [] t  in
          (match uu____26078 with
           | (us1,uu____26102,t1) ->
               let uu___362_26124 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___362_26124.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___362_26124.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___362_26124.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___362_26124.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____26125 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____26127 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____26127 with
           | (univs1,binders,signature) ->
               let uu____26167 =
                 let uu____26172 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____26172 with
                 | (univs_opening,univs2) ->
                     let uu____26195 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____26195)
                  in
               (match uu____26167 with
                | (univs_opening,univs_closing) ->
                    let uu____26198 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____26204 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____26205 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____26204, uu____26205)  in
                    (match uu____26198 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____26231 =
                           match uu____26231 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____26249 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____26249 with
                                | (us1,t1) ->
                                    let uu____26260 =
                                      let uu____26269 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____26280 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____26269, uu____26280)  in
                                    (match uu____26260 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____26309 =
                                           let uu____26318 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____26329 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____26318, uu____26329)  in
                                         (match uu____26309 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____26359 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____26359
                                                 in
                                              let uu____26360 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____26360 with
                                               | (uu____26387,uu____26388,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____26411 =
                                                       let uu____26412 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____26412
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____26411
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____26421 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____26421 with
                           | (uu____26440,uu____26441,t1) -> t1  in
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
                             | uu____26517 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____26544 =
                               let uu____26545 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____26545.FStar_Syntax_Syntax.n  in
                             match uu____26544 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____26604 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____26637 =
                               let uu____26638 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____26638.FStar_Syntax_Syntax.n  in
                             match uu____26637 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____26661) ->
                                 let uu____26686 = destruct_action_body body
                                    in
                                 (match uu____26686 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____26735 ->
                                 let uu____26736 = destruct_action_body t  in
                                 (match uu____26736 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____26791 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____26791 with
                           | (action_univs,t) ->
                               let uu____26800 = destruct_action_typ_templ t
                                  in
                               (match uu____26800 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___363_26847 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___363_26847.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___363_26847.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___364_26849 = ed  in
                           let uu____26850 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____26851 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____26852 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____26853 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____26854 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____26855 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____26856 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____26857 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____26858 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____26859 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____26860 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____26861 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____26862 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____26863 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___364_26849.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___364_26849.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____26850;
                             FStar_Syntax_Syntax.bind_wp = uu____26851;
                             FStar_Syntax_Syntax.if_then_else = uu____26852;
                             FStar_Syntax_Syntax.ite_wp = uu____26853;
                             FStar_Syntax_Syntax.stronger = uu____26854;
                             FStar_Syntax_Syntax.close_wp = uu____26855;
                             FStar_Syntax_Syntax.assert_p = uu____26856;
                             FStar_Syntax_Syntax.assume_p = uu____26857;
                             FStar_Syntax_Syntax.null_wp = uu____26858;
                             FStar_Syntax_Syntax.trivial = uu____26859;
                             FStar_Syntax_Syntax.repr = uu____26860;
                             FStar_Syntax_Syntax.return_repr = uu____26861;
                             FStar_Syntax_Syntax.bind_repr = uu____26862;
                             FStar_Syntax_Syntax.actions = uu____26863;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___364_26849.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___365_26866 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___365_26866.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___365_26866.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___365_26866.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___365_26866.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___267_26887 =
            match uu___267_26887 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____26918 = elim_uvars_aux_t env us [] t  in
                (match uu____26918 with
                 | (us1,uu____26950,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___366_26981 = sub_eff  in
            let uu____26982 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____26985 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___366_26981.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___366_26981.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____26982;
              FStar_Syntax_Syntax.lift = uu____26985
            }  in
          let uu___367_26988 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___367_26988.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___367_26988.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___367_26988.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___367_26988.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____26998 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____26998 with
           | (univ_names1,binders1,comp1) ->
               let uu___368_27038 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___368_27038.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___368_27038.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___368_27038.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___368_27038.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____27041 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____27042 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      normalize
        [FStar_TypeChecker_Env.EraseUniverses;
        FStar_TypeChecker_Env.AllowUnboundUniverses] env t
  