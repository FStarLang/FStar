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
        let uu____1284 = FStar_List.nth env x.FStar_Syntax_Syntax.index  in
        FStar_Pervasives_Native.snd uu____1284
      with
      | uu____1303 ->
          let uu____1304 =
            let uu____1305 = FStar_Syntax_Print.db_to_string x  in
            let uu____1306 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____1305
              uu____1306
             in
          failwith uu____1304
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____1314 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____1314
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____1318 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____1318
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____1322 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____1322
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
          let uu____1356 =
            FStar_List.fold_left
              (fun uu____1382  ->
                 fun u1  ->
                   match uu____1382 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1407 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____1407 with
                        | (k_u,n1) ->
                            let uu____1422 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____1422
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____1356 with
          | (uu____1440,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 let uu____1468 =
                   let uu____1469 = FStar_List.nth env x  in
                   FStar_Pervasives_Native.snd uu____1469  in
                 match uu____1468 with
                 | Univ u3 ->
                     ((let uu____1488 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug
                              cfg.FStar_TypeChecker_Cfg.tcenv)
                           (FStar_Options.Other "univ_norm")
                          in
                       if uu____1488
                       then
                         let uu____1489 =
                           FStar_Syntax_Print.univ_to_string u3  in
                         FStar_Util.print1 "Univ (in norm_universe): %s\n"
                           uu____1489
                       else ());
                      aux u3)
                 | Dummy  -> [u2]
                 | uu____1491 ->
                     let uu____1492 =
                       let uu____1493 = FStar_Util.string_of_int x  in
                       FStar_Util.format1
                         "Impossible: universe variable u@%s bound to a term"
                         uu____1493
                        in
                     failwith uu____1492
               with
               | uu____1501 ->
                   if
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else
                     (let uu____1505 =
                        let uu____1506 = FStar_Util.string_of_int x  in
                        Prims.strcat "Universe variable not found: u@"
                          uu____1506
                         in
                      failwith uu____1505))
          | FStar_Syntax_Syntax.U_unif uu____1509 when
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1518 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1527 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1534 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____1534 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____1551 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____1551 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1559 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1567 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____1567 with
                                  | (uu____1572,m) -> n1 <= m))
                           in
                        if uu____1559 then rest1 else us1
                    | uu____1577 -> us1)
               | uu____1582 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1586 = aux u3  in
              FStar_List.map (fun _0_16  -> FStar_Syntax_Syntax.U_succ _0_16)
                uu____1586
           in
        if
          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1590 = aux u  in
           match uu____1590 with
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
            (fun uu____1742  ->
               let uu____1743 = FStar_Syntax_Print.tag_of_term t  in
               let uu____1744 = env_to_string env  in
               let uu____1745 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____1743 uu____1744 uu____1745);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____1754 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____1757 ->
                    let uu____1780 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____1780
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____1781 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____1782 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____1783 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____1784 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____1808 ->
                           let uu____1821 =
                             let uu____1822 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____1823 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____1822 uu____1823
                              in
                           failwith uu____1821
                       | uu____1826 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___252_1861  ->
                                         match uu___252_1861 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____1868 =
                                               let uu____1875 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____1875)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____1868
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___272_1885 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___272_1885.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___272_1885.FStar_Syntax_Syntax.sort)
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
                                              | uu____1890 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____1893 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___273_1897 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___273_1897.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___273_1897.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____1918 =
                        let uu____1919 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____1919  in
                      mk uu____1918 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____1927 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1927  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____1929 = lookup_bvar env x  in
                    (match uu____1929 with
                     | Univ uu____1932 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___274_1936 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___274_1936.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___274_1936.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____1942,uu____1943) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____2032  ->
                              fun stack1  ->
                                match uu____2032 with
                                | (a,aq) ->
                                    let uu____2044 =
                                      let uu____2045 =
                                        let uu____2052 =
                                          let uu____2053 =
                                            let uu____2084 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____2084, false)  in
                                          Clos uu____2053  in
                                        (uu____2052, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____2045  in
                                    uu____2044 :: stack1) args)
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
                    let uu____2272 = close_binders cfg env bs  in
                    (match uu____2272 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____2327 =
                      let uu____2340 =
                        let uu____2349 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____2349]  in
                      close_binders cfg env uu____2340  in
                    (match uu____2327 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____2394 =
                             let uu____2395 =
                               let uu____2402 =
                                 let uu____2403 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____2403
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____2402, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____2395  in
                           mk uu____2394 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____2502 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____2502
                      | FStar_Util.Inr c ->
                          let uu____2516 = close_comp cfg env c  in
                          FStar_Util.Inr uu____2516
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____2535 =
                        let uu____2536 =
                          let uu____2563 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____2563, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____2536  in
                      mk uu____2535 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____2609 =
                            let uu____2610 =
                              let uu____2617 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____2617, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____2610  in
                          mk uu____2609 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____2669  -> dummy :: env1) env
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
                    let uu____2690 =
                      let uu____2701 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____2701
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____2720 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___275_2736 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___275_2736.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___275_2736.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____2720))
                       in
                    (match uu____2690 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___276_2754 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___276_2754.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___276_2754.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___276_2754.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___276_2754.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____2768,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____2831  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____2848 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____2848
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____2860  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____2884 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____2884
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___277_2892 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___277_2892.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___277_2892.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___278_2893 = lb  in
                      let uu____2894 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___278_2893.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___278_2893.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____2894;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___278_2893.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___278_2893.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____2926  -> fun env1  -> dummy :: env1)
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
            (fun uu____3015  ->
               let uu____3016 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3017 = env_to_string env  in
               let uu____3018 = stack_to_string stack  in
               let uu____3019 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____3016 uu____3017 uu____3018 uu____3019);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____3024,uu____3025),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____3104 = close_binders cfg env' bs  in
               (match uu____3104 with
                | (bs1,uu____3120) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____3140 =
                      let uu___279_3143 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___279_3143.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___279_3143.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____3140)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____3199 =
                 match uu____3199 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____3314 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____3343 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____3427  ->
                                     fun uu____3428  ->
                                       match (uu____3427, uu____3428) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____3567 = norm_pat env4 p1
                                              in
                                           (match uu____3567 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____3343 with
                            | (pats1,env4) ->
                                ((let uu___280_3729 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___280_3729.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___281_3748 = x  in
                             let uu____3749 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___281_3748.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___281_3748.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3749
                             }  in
                           ((let uu___282_3763 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___282_3763.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___283_3774 = x  in
                             let uu____3775 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___283_3774.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___283_3774.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3775
                             }  in
                           ((let uu___284_3789 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___284_3789.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___285_3805 = x  in
                             let uu____3806 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___285_3805.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___285_3805.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3806
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___286_3823 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___286_3823.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____3828 = norm_pat env2 pat  in
                     (match uu____3828 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____3897 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____3897
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____3916 =
                   let uu____3917 =
                     let uu____3940 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____3940)  in
                   FStar_Syntax_Syntax.Tm_match uu____3917  in
                 mk uu____3916 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____4055 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____4164  ->
                                       match uu____4164 with
                                       | (a,q) ->
                                           let uu____4191 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____4191, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____4055
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____4204 =
                       let uu____4211 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____4211)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____4204
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____4223 =
                       let uu____4232 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____4232)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____4223
                 | uu____4237 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____4243 -> failwith "Impossible: unexpected stack element")

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
        let uu____4259 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4342  ->
                  fun uu____4343  ->
                    match (uu____4342, uu____4343) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___287_4483 = b  in
                          let uu____4484 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___287_4483.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___287_4483.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4484
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____4259 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____4621 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4634 = inline_closure_env cfg env [] t  in
                 let uu____4635 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____4634 uu____4635
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4648 = inline_closure_env cfg env [] t  in
                 let uu____4649 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4648 uu____4649
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____4703  ->
                           match uu____4703 with
                           | (a,q) ->
                               let uu____4724 =
                                 inline_closure_env cfg env [] a  in
                               (uu____4724, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___253_4741  ->
                           match uu___253_4741 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4745 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____4745
                           | f -> f))
                    in
                 let uu____4749 =
                   let uu___288_4750 = c1  in
                   let uu____4751 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4751;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___288_4750.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____4749)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___254_4761  ->
            match uu___254_4761 with
            | FStar_Syntax_Syntax.DECREASES uu____4762 -> false
            | uu____4765 -> true))

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
                   (fun uu___255_4783  ->
                      match uu___255_4783 with
                      | FStar_Syntax_Syntax.DECREASES uu____4784 -> false
                      | uu____4787 -> true))
               in
            let rc1 =
              let uu___289_4789 = rc  in
              let uu____4790 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___289_4789.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4790;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____4799 -> lopt

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
    let uu____4866 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____4866 with
    | FStar_Pervasives_Native.Some e ->
        let uu____4905 = FStar_Syntax_Embeddings.unembed e t  in
        uu____4905 true FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____4925 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____4925) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____4987  ->
           fun subst1  ->
             match uu____4987 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____5028,uu____5029)) ->
                      let uu____5088 = b  in
                      (match uu____5088 with
                       | (bv,uu____5096) ->
                           let uu____5097 =
                             let uu____5098 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____5098  in
                           if uu____5097
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____5103 = unembed_binder term1  in
                              match uu____5103 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____5110 =
                                      let uu___290_5111 = bv  in
                                      let uu____5112 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___290_5111.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___290_5111.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____5112
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____5110
                                     in
                                  let b_for_x =
                                    let uu____5118 =
                                      let uu____5125 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____5125)
                                       in
                                    FStar_Syntax_Syntax.NT uu____5118  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___256_5141  ->
                                         match uu___256_5141 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____5142,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____5144;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____5145;_})
                                             ->
                                             let uu____5150 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____5150
                                         | uu____5151 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____5152 -> subst1)) env []
  
let reduce_primops :
  'Auu____5174 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv,'Auu____5174) FStar_Pervasives_Native.tuple2
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
            (let uu____5226 = FStar_Syntax_Util.head_and_args tm  in
             match uu____5226 with
             | (head1,args) ->
                 let uu____5271 =
                   let uu____5272 = FStar_Syntax_Util.un_uinst head1  in
                   uu____5272.FStar_Syntax_Syntax.n  in
                 (match uu____5271 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____5278 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                      (match uu____5278 with
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
                                (fun uu____5306  ->
                                   let uu____5307 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name
                                      in
                                   let uu____5308 =
                                     FStar_Util.string_of_int l  in
                                   let uu____5315 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____5307 uu____5308 uu____5315);
                              tm)
                           else
                             (let uu____5317 =
                                if l = prim_step.FStar_TypeChecker_Cfg.arity
                                then (args, [])
                                else
                                  FStar_List.splitAt
                                    prim_step.FStar_TypeChecker_Cfg.arity
                                    args
                                 in
                              match uu____5317 with
                              | (args_1,args_2) ->
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____5454  ->
                                        let uu____5455 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____5455);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____5458  ->
                                             if
                                               prim_step.FStar_TypeChecker_Cfg.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____5460 =
                                      prim_step.FStar_TypeChecker_Cfg.interpretation
                                        psc norm_cb args_1
                                       in
                                    match uu____5460 with
                                    | FStar_Pervasives_Native.None  ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5470  ->
                                              let uu____5471 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____5471);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5477  ->
                                              let uu____5478 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____5479 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____5478 uu____5479);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____5480 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____5484  ->
                                 let uu____5485 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____5485);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5489  ->
                            let uu____5490 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5490);
                       (match args with
                        | (a1,uu____5494)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____5519 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5533  ->
                            let uu____5534 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5534);
                       (match args with
                        | (t,uu____5538)::(r,uu____5540)::[] ->
                            let uu____5581 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____5581 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____5587 -> tm))
                  | uu____5598 -> tm))
  
let reduce_equality :
  'Auu____5609 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv,'Auu____5609) FStar_Pervasives_Native.tuple2
           FStar_Pervasives_Native.option,closure)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun tm  ->
        reduce_primops norm_cb
          (let uu___291_5662 = cfg  in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___292_5665 = FStar_TypeChecker_Cfg.default_steps  in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___292_5665.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___292_5665.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___292_5665.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___292_5665.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___292_5665.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___292_5665.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___292_5665.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___292_5665.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___292_5665.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___292_5665.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___292_5665.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___292_5665.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___292_5665.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___292_5665.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___292_5665.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___292_5665.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___292_5665.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___292_5665.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___292_5665.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___292_5665.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___292_5665.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___292_5665.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___292_5665.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___292_5665.FStar_TypeChecker_Cfg.nbe_step)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___291_5662.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___291_5662.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___291_5662.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___291_5662.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___291_5662.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___291_5662.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___291_5662.FStar_TypeChecker_Cfg.reifying)
           }) tm
  
let is_norm_request :
  'Auu____5672 .
    FStar_Syntax_Syntax.term -> 'Auu____5672 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____5687 =
        let uu____5694 =
          let uu____5695 = FStar_Syntax_Util.un_uinst hd1  in
          uu____5695.FStar_Syntax_Syntax.n  in
        (uu____5694, args)  in
      match uu____5687 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5701::uu____5702::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5706::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____5711::uu____5712::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____5715 -> false
  
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s  ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
  
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___257_5737  ->
    match uu___257_5737 with
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
        let uu____5743 =
          let uu____5746 =
            let uu____5747 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldOnly uu____5747  in
          [uu____5746]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____5743
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____5753 =
          let uu____5756 =
            let uu____5757 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldFully uu____5757  in
          [uu____5756]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____5753
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.UnfoldAttr t]
    | FStar_Syntax_Embeddings.NBE  -> [FStar_TypeChecker_Env.NBE]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  = fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____5780 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term,'Auu____5780)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____5831 =
            let uu____5836 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____5836 s  in
          match uu____5831 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____5852 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____5852
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
        | uu____5878::(tm,uu____5880)::[] ->
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
        | (tm,uu____5909)::[] ->
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
        | (steps,uu____5930)::uu____5931::(tm,uu____5933)::[] ->
            let add_exclude s z =
              let uu____5971 =
                FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s  in
              if uu____5971
              then s
              else (FStar_TypeChecker_Env.Exclude z) :: s  in
            let uu____5975 =
              let uu____5980 = full_norm steps  in parse_steps uu____5980  in
            (match uu____5975 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = FStar_TypeChecker_Env.Beta :: s  in
                 let s2 = add_exclude s1 FStar_TypeChecker_Env.Zeta  in
                 let s3 = add_exclude s2 FStar_TypeChecker_Env.Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____6019 -> FStar_Pervasives_Native.None
  
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun s  ->
      fun tm  ->
        let delta_level =
          let uu____6050 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___258_6055  ->
                    match uu___258_6055 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____6056 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____6057 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____6060 -> true
                    | uu____6063 -> false))
             in
          if uu____6050
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta]  in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____6070  ->
             let uu____6071 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____6071);
        (let tm_norm =
           let uu____6073 =
             let uu____6088 = FStar_TypeChecker_Cfg.cfg_env cfg  in
             uu____6088.FStar_TypeChecker_Env.nbe  in
           uu____6073 s cfg.FStar_TypeChecker_Cfg.tcenv tm  in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____6092  ->
              let uu____6093 = FStar_Syntax_Print.term_to_string tm_norm  in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____6093);
         tm_norm)
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___259_6100  ->
    match uu___259_6100 with
    | (App
        (uu____6103,{
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reify );
                      FStar_Syntax_Syntax.pos = uu____6104;
                      FStar_Syntax_Syntax.vars = uu____6105;_},uu____6106,uu____6107))::uu____6108
        -> true
    | uu____6113 -> false
  
let firstn :
  'Auu____6122 .
    Prims.int ->
      'Auu____6122 Prims.list ->
        ('Auu____6122 Prims.list,'Auu____6122 Prims.list)
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
          (uu____6164,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____6165;
                        FStar_Syntax_Syntax.vars = uu____6166;_},uu____6167,uu____6168))::uu____6169
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____6174 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____6197) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____6207) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____6228  ->
                  match uu____6228 with
                  | (a,uu____6238) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6248 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____6271 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____6272 -> false
    | FStar_Syntax_Syntax.Tm_type uu____6285 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____6286 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____6287 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____6288 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____6289 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____6290 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____6297 -> false
    | FStar_Syntax_Syntax.Tm_let uu____6304 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____6317 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____6336 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____6351 -> true
    | FStar_Syntax_Syntax.Tm_match uu____6358 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____6428  ->
                   match uu____6428 with
                   | (a,uu____6438) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____6449) ->
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
                     (fun uu____6577  ->
                        match uu____6577 with
                        | (a,uu____6587) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____6596,uu____6597,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____6603,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____6609 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____6616 -> false
            | FStar_Syntax_Syntax.Meta_named uu____6617 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____6623 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____6629 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_fully  -> true | uu____6635 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_reify  -> true | uu____6641 -> false
  
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
            let uu____6670 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
            match uu____6670 with
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
              (fun uu____6798  ->
                 fun uu____6799  ->
                   match (uu____6798, uu____6799) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____6859 =
            match uu____6859 with
            | (x,y,z) ->
                let uu____6869 = FStar_Util.string_of_bool x  in
                let uu____6870 = FStar_Util.string_of_bool y  in
                let uu____6871 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____6869 uu____6870
                  uu____6871
             in
          let res =
            match (qninfo,
                    ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only),
                    ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully),
                    ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr))
            with
            | uu____6917 when FStar_TypeChecker_Env.qninfo_is_action qninfo
                ->
                let b = should_reify1 cfg  in
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____6963  ->
                      let uu____6964 = FStar_Syntax_Print.fv_to_string fv  in
                      let uu____6965 = FStar_Util.string_of_bool b  in
                      FStar_Util.print2
                        "should_unfold: For DM4F action %s, should_reify = %s\n"
                        uu____6964 uu____6965);
                 if b then reif else no)
            | uu____6973 when
                let uu____7014 = FStar_TypeChecker_Cfg.find_prim_step cfg fv
                   in
                FStar_Option.isSome uu____7014 ->
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7019  ->
                      FStar_Util.print_string
                        " >> It's a primop, not unfolding\n");
                 no)
            | (FStar_Pervasives_Native.Some
               (FStar_Util.Inr
                ({
                   FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                     ((is_rec,uu____7021),uu____7022);
                   FStar_Syntax_Syntax.sigrng = uu____7023;
                   FStar_Syntax_Syntax.sigquals = qs;
                   FStar_Syntax_Syntax.sigmeta = uu____7025;
                   FStar_Syntax_Syntax.sigattrs = uu____7026;_},uu____7027),uu____7028),uu____7029,uu____7030,uu____7031)
                when
                FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect qs ->
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7136  ->
                      FStar_Util.print_string
                        " >> HasMaskedEffect, not unfolding\n");
                 no)
            | (uu____7137,uu____7138,uu____7139,uu____7140) when
                (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                  &&
                  (FStar_Util.for_some
                     (FStar_Syntax_Util.attr_eq
                        FStar_Syntax_Util.tac_opaque_attr) attrs)
                ->
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7207  ->
                      FStar_Util.print_string
                        " >> tac_opaque, not unfolding\n");
                 no)
            | (FStar_Pervasives_Native.Some
               (FStar_Util.Inr
                ({
                   FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                     ((is_rec,uu____7209),uu____7210);
                   FStar_Syntax_Syntax.sigrng = uu____7211;
                   FStar_Syntax_Syntax.sigquals = qs;
                   FStar_Syntax_Syntax.sigmeta = uu____7213;
                   FStar_Syntax_Syntax.sigattrs = uu____7214;_},uu____7215),uu____7216),uu____7217,uu____7218,uu____7219)
                when
                is_rec &&
                  (Prims.op_Negation
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                ->
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7324  ->
                      FStar_Util.print_string
                        " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                 no)
            | (uu____7325,FStar_Pervasives_Native.Some
               uu____7326,uu____7327,uu____7328) ->
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7396  ->
                      let uu____7397 = FStar_Syntax_Print.fv_to_string fv  in
                      FStar_Util.print1
                        "should_unfold: Reached a %s with selective unfolding\n"
                        uu____7397);
                 (let uu____7398 =
                    let uu____7407 =
                      match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                      with
                      | FStar_Pervasives_Native.None  -> no
                      | FStar_Pervasives_Native.Some lids ->
                          let uu____7427 =
                            FStar_Util.for_some
                              (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                             in
                          FStar_All.pipe_left yesno uu____7427
                       in
                    let uu____7434 =
                      let uu____7443 =
                        match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                        with
                        | FStar_Pervasives_Native.None  -> no
                        | FStar_Pervasives_Native.Some ats ->
                            let uu____7463 =
                              FStar_Util.for_some
                                (fun at  ->
                                   FStar_Util.for_some
                                     (FStar_Syntax_Util.attr_eq at) ats)
                                attrs
                               in
                            FStar_All.pipe_left yesno uu____7463
                         in
                      let uu____7472 =
                        let uu____7481 =
                          match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                          with
                          | FStar_Pervasives_Native.None  -> no
                          | FStar_Pervasives_Native.Some lids ->
                              let uu____7501 =
                                FStar_Util.for_some
                                  (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                 in
                              FStar_All.pipe_left fullyno uu____7501
                           in
                        [uu____7481]  in
                      uu____7443 :: uu____7472  in
                    uu____7407 :: uu____7434  in
                  comb_or uu____7398))
            | (uu____7532,uu____7533,FStar_Pervasives_Native.Some
               uu____7534,uu____7535) ->
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7603  ->
                      let uu____7604 = FStar_Syntax_Print.fv_to_string fv  in
                      FStar_Util.print1
                        "should_unfold: Reached a %s with selective unfolding\n"
                        uu____7604);
                 (let uu____7605 =
                    let uu____7614 =
                      match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                      with
                      | FStar_Pervasives_Native.None  -> no
                      | FStar_Pervasives_Native.Some lids ->
                          let uu____7634 =
                            FStar_Util.for_some
                              (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                             in
                          FStar_All.pipe_left yesno uu____7634
                       in
                    let uu____7641 =
                      let uu____7650 =
                        match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                        with
                        | FStar_Pervasives_Native.None  -> no
                        | FStar_Pervasives_Native.Some ats ->
                            let uu____7670 =
                              FStar_Util.for_some
                                (fun at  ->
                                   FStar_Util.for_some
                                     (FStar_Syntax_Util.attr_eq at) ats)
                                attrs
                               in
                            FStar_All.pipe_left yesno uu____7670
                         in
                      let uu____7679 =
                        let uu____7688 =
                          match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                          with
                          | FStar_Pervasives_Native.None  -> no
                          | FStar_Pervasives_Native.Some lids ->
                              let uu____7708 =
                                FStar_Util.for_some
                                  (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                 in
                              FStar_All.pipe_left fullyno uu____7708
                           in
                        [uu____7688]  in
                      uu____7650 :: uu____7679  in
                    uu____7614 :: uu____7641  in
                  comb_or uu____7605))
            | (uu____7739,uu____7740,uu____7741,FStar_Pervasives_Native.Some
               uu____7742) ->
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7810  ->
                      let uu____7811 = FStar_Syntax_Print.fv_to_string fv  in
                      FStar_Util.print1
                        "should_unfold: Reached a %s with selective unfolding\n"
                        uu____7811);
                 (let uu____7812 =
                    let uu____7821 =
                      match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                      with
                      | FStar_Pervasives_Native.None  -> no
                      | FStar_Pervasives_Native.Some lids ->
                          let uu____7841 =
                            FStar_Util.for_some
                              (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                             in
                          FStar_All.pipe_left yesno uu____7841
                       in
                    let uu____7848 =
                      let uu____7857 =
                        match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                        with
                        | FStar_Pervasives_Native.None  -> no
                        | FStar_Pervasives_Native.Some ats ->
                            let uu____7877 =
                              FStar_Util.for_some
                                (fun at  ->
                                   FStar_Util.for_some
                                     (FStar_Syntax_Util.attr_eq at) ats)
                                attrs
                               in
                            FStar_All.pipe_left yesno uu____7877
                         in
                      let uu____7886 =
                        let uu____7895 =
                          match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                          with
                          | FStar_Pervasives_Native.None  -> no
                          | FStar_Pervasives_Native.Some lids ->
                              let uu____7915 =
                                FStar_Util.for_some
                                  (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                 in
                              FStar_All.pipe_left fullyno uu____7915
                           in
                        [uu____7895]  in
                      uu____7857 :: uu____7886  in
                    uu____7821 :: uu____7848  in
                  comb_or uu____7812))
            | uu____7946 ->
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7992  ->
                      let uu____7993 = FStar_Syntax_Print.fv_to_string fv  in
                      let uu____7994 =
                        FStar_Syntax_Print.delta_depth_to_string
                          fv.FStar_Syntax_Syntax.fv_delta
                         in
                      let uu____7995 =
                        FStar_Common.string_of_list
                          FStar_TypeChecker_Env.string_of_delta_level
                          cfg.FStar_TypeChecker_Cfg.delta_level
                         in
                      FStar_Util.print3
                        "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                        uu____7993 uu____7994 uu____7995);
                 (let uu____7996 =
                    FStar_All.pipe_right
                      cfg.FStar_TypeChecker_Cfg.delta_level
                      (FStar_Util.for_some
                         (fun uu___260_8000  ->
                            match uu___260_8000 with
                            | FStar_TypeChecker_Env.NoDelta  -> false
                            | FStar_TypeChecker_Env.InliningDelta  -> true
                            | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                                true
                            | FStar_TypeChecker_Env.Unfold l ->
                                FStar_TypeChecker_Common.delta_depth_greater_than
                                  fv.FStar_Syntax_Syntax.fv_delta l))
                     in
                  FStar_All.pipe_left yesno uu____7996))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____8013  ->
               let uu____8014 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____8015 =
                 let uu____8016 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____8016  in
               let uu____8017 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____8014 uu____8015 uu____8017);
          (match res with
           | (false ,uu____8018,uu____8019) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____8020 ->
               let uu____8027 =
                 let uu____8028 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____8028
                  in
               FStar_All.pipe_left failwith uu____8027)
  
let decide_unfolding :
  'Auu____8045 'Auu____8046 .
    FStar_TypeChecker_Cfg.cfg ->
      'Auu____8045 ->
        stack_elt Prims.list ->
          'Auu____8046 ->
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
                    let uu___293_8115 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___294_8118 = cfg.FStar_TypeChecker_Cfg.steps
                            in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___294_8118.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___294_8118.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___294_8118.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___294_8118.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___294_8118.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___294_8118.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___294_8118.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___294_8118.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___294_8118.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___294_8118.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___294_8118.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___294_8118.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___294_8118.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___294_8118.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___294_8118.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___294_8118.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___294_8118.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___294_8118.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___294_8118.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___294_8118.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___294_8118.FStar_TypeChecker_Cfg.nbe_step)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___293_8115.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___293_8115.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___293_8115.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___293_8115.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___293_8115.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___293_8115.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___293_8115.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___293_8115.FStar_TypeChecker_Cfg.reifying)
                    }  in
                  let stack' = (Cfg cfg) :: stack  in
                  FStar_Pervasives_Native.Some (cfg', stack')
              | Should_unfold_reify  ->
                  let uu____8136 =
                    let uu____8143 = FStar_List.tl stack  in
                    (cfg, uu____8143)  in
                  FStar_Pervasives_Native.Some uu____8136
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____8430 ->
                   let uu____8453 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____8453
               | uu____8454 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____8463  ->
               let uu____8464 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____8465 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____8466 = FStar_Syntax_Print.term_to_string t1  in
               let uu____8467 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____8474 =
                 let uu____8475 =
                   let uu____8478 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8478
                    in
                 stack_to_string uu____8475  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____8464 uu____8465 uu____8466 uu____8467 uu____8474);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____8504  ->
               let uu____8505 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____8505);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8509  ->
                     let uu____8510 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8510);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____8511 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8515  ->
                     let uu____8516 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8516);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____8517 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8521  ->
                     let uu____8522 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8522);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____8523 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8527  ->
                     let uu____8528 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8528);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8529;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_17;
                 FStar_Syntax_Syntax.fv_qual = uu____8530;_}
               when _0_17 = (Prims.parse_int "0") ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8536  ->
                     let uu____8537 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8537);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8538;
                 FStar_Syntax_Syntax.fv_delta = uu____8539;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8543  ->
                     let uu____8544 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8544);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8545;
                 FStar_Syntax_Syntax.fv_delta = uu____8546;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____8547);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8557  ->
                     let uu____8558 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8558);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____8561 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv uu____8561
                  in
               let uu____8562 =
                 decide_unfolding cfg env stack t1.FStar_Syntax_Syntax.pos fv
                   qninfo
                  in
               (match uu____8562 with
                | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                    do_unfold_fv cfg1 env stack1 t1 qninfo fv
                | FStar_Pervasives_Native.None  -> rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_quoted uu____8589 ->
               let uu____8596 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____8596
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
                  && (is_norm_request hd1 args))
                 &&
                 (let uu____8632 =
                    FStar_Ident.lid_equals
                      (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____8632)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___295_8636 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___296_8639 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___296_8639.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___296_8639.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___296_8639.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___296_8639.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___296_8639.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___296_8639.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___296_8639.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___296_8639.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___296_8639.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___296_8639.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___296_8639.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___296_8639.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___296_8639.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___296_8639.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___296_8639.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___296_8639.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___296_8639.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___296_8639.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___296_8639.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___296_8639.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___296_8639.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___296_8639.FStar_TypeChecker_Cfg.nbe_step)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___295_8636.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___295_8636.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___295_8636.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___295_8636.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___295_8636.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___295_8636.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____8644 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____8644 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____8677  ->
                                 fun stack1  ->
                                   match uu____8677 with
                                   | (a,aq) ->
                                       let uu____8689 =
                                         let uu____8690 =
                                           let uu____8697 =
                                             let uu____8698 =
                                               let uu____8729 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____8729, false)
                                                in
                                             Clos uu____8698  in
                                           (uu____8697, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____8690  in
                                       uu____8689 :: stack1) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____8817  ->
                            let uu____8818 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____8818);
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
                        (let uu____8854 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting norm request on %s ... \n" uu____8854)
                      else ();
                      (let delta_level =
                         let uu____8859 =
                           FStar_All.pipe_right s
                             (FStar_Util.for_some
                                (fun uu___261_8864  ->
                                   match uu___261_8864 with
                                   | FStar_TypeChecker_Env.UnfoldUntil
                                       uu____8865 -> true
                                   | FStar_TypeChecker_Env.UnfoldOnly
                                       uu____8866 -> true
                                   | FStar_TypeChecker_Env.UnfoldFully
                                       uu____8869 -> true
                                   | uu____8872 -> false))
                            in
                         if uu____8859
                         then
                           [FStar_TypeChecker_Env.Unfold
                              FStar_Syntax_Syntax.delta_constant]
                         else [FStar_TypeChecker_Env.NoDelta]  in
                       let cfg'1 =
                         let uu___297_8877 = cfg  in
                         let uu____8878 =
                           let uu___298_8879 =
                             FStar_TypeChecker_Cfg.to_fsteps s  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___298_8879.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___298_8879.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___298_8879.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak =
                               (uu___298_8879.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___298_8879.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___298_8879.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___298_8879.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___298_8879.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               (uu___298_8879.FStar_TypeChecker_Cfg.unfold_only);
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___298_8879.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___298_8879.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___298_8879.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___298_8879.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___298_8879.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___298_8879.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___298_8879.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___298_8879.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___298_8879.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___298_8879.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___298_8879.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___298_8879.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___298_8879.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               true;
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___298_8879.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___298_8879.FStar_TypeChecker_Cfg.nbe_step)
                           }  in
                         {
                           FStar_TypeChecker_Cfg.steps = uu____8878;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___297_8877.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___297_8877.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = delta_level;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___297_8877.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong =
                             (uu___297_8877.FStar_TypeChecker_Cfg.strong);
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___297_8877.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___297_8877.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let stack' =
                         let tail1 = (Cfg cfg) :: stack  in
                         if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           let uu____8884 =
                             let uu____8885 =
                               let uu____8890 = FStar_Util.now ()  in
                               (t1, uu____8890)  in
                             Debug uu____8885  in
                           uu____8884 :: tail1
                         else tail1  in
                       norm cfg'1 env stack' tm))))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____8894 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____8894
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____8903 =
                      let uu____8910 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____8910, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____8903  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____8919 = lookup_bvar env x  in
               (match uu____8919 with
                | Univ uu____8920 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                    then
                      let uu____8969 = FStar_ST.op_Bang r  in
                      (match uu____8969 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9087  ->
                                 let uu____9088 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____9089 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____9088
                                   uu____9089);
                            (let uu____9090 = maybe_weakly_reduced t'  in
                             if uu____9090
                             then
                               match stack with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____9091 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____9166)::uu____9167 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____9177,uu____9178))::stack_rest ->
                    (match c with
                     | Univ uu____9182 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____9191 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____9220  ->
                                    let uu____9221 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____9221);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____9255  ->
                                    let uu____9256 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____9256);
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
                       (fun uu____9324  ->
                          let uu____9325 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____9325);
                     norm cfg env stack1 t1)
                | (Match uu____9326)::uu____9327 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9340 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9340 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9376  -> dummy :: env1) env)
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
                                          let uu____9419 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9419)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___299_9426 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___299_9426.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___299_9426.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9427 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9433  ->
                                 let uu____9434 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9434);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___300_9445 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___300_9445.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___300_9445.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___300_9445.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___300_9445.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___300_9445.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___300_9445.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___300_9445.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___300_9445.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____9448)::uu____9449 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9458 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9458 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9494  -> dummy :: env1) env)
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
                                          let uu____9537 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9537)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___299_9544 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___299_9544.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___299_9544.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9545 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9551  ->
                                 let uu____9552 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9552);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___300_9563 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___300_9563.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___300_9563.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___300_9563.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___300_9563.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___300_9563.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___300_9563.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___300_9563.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___300_9563.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____9566)::uu____9567 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9578 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9578 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9614  -> dummy :: env1) env)
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
                                          let uu____9657 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9657)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___299_9664 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___299_9664.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___299_9664.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9665 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9671  ->
                                 let uu____9672 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9672);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___300_9683 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___300_9683.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___300_9683.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___300_9683.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___300_9683.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___300_9683.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___300_9683.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___300_9683.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___300_9683.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____9686)::uu____9687 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9700 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9700 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9736  -> dummy :: env1) env)
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
                                          let uu____9779 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9779)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___299_9786 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___299_9786.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___299_9786.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9787 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9793  ->
                                 let uu____9794 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9794);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___300_9805 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___300_9805.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___300_9805.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___300_9805.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___300_9805.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___300_9805.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___300_9805.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___300_9805.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___300_9805.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____9808)::uu____9809 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9822 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9822 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9858  -> dummy :: env1) env)
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
                                          let uu____9901 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9901)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___299_9908 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___299_9908.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___299_9908.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9909 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9915  ->
                                 let uu____9916 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9916);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___300_9927 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___300_9927.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___300_9927.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___300_9927.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___300_9927.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___300_9927.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___300_9927.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___300_9927.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___300_9927.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____9930)::uu____9931 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9948 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9948 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9984  -> dummy :: env1) env)
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
                                          let uu____10027 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10027)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___299_10034 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___299_10034.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___299_10034.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10035 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10041  ->
                                 let uu____10042 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10042);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___300_10053 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___300_10053.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___300_10053.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___300_10053.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___300_10053.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___300_10053.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___300_10053.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___300_10053.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___300_10053.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____10058 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10058 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10094  -> dummy :: env1) env)
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
                                          let uu____10137 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10137)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___299_10144 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___299_10144.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___299_10144.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10145 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10151  ->
                                 let uu____10152 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10152);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___300_10163 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___300_10163.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___300_10163.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___300_10163.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___300_10163.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___300_10163.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___300_10163.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___300_10163.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___300_10163.FStar_TypeChecker_Cfg.reifying)
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
                      (fun uu____10206  ->
                         fun stack1  ->
                           match uu____10206 with
                           | (a,aq) ->
                               let uu____10218 =
                                 let uu____10219 =
                                   let uu____10226 =
                                     let uu____10227 =
                                       let uu____10258 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____10258, false)  in
                                     Clos uu____10227  in
                                   (uu____10226, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____10219  in
                               uu____10218 :: stack1) args)
                  in
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____10346  ->
                     let uu____10347 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____10347);
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
                             ((let uu___301_10395 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___301_10395.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___301_10395.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____10396 ->
                      let uu____10411 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10411)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____10414 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____10414 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____10445 =
                          let uu____10446 =
                            let uu____10453 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___302_10459 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___302_10459.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___302_10459.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____10453)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____10446  in
                        mk uu____10445 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____10482 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____10482
               else
                 (let uu____10484 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____10484 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____10492 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____10518  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____10492 c1  in
                      let t2 =
                        let uu____10542 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____10542 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____10655)::uu____10656 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10669  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____10670)::uu____10671 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10682  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____10683,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____10684;
                                   FStar_Syntax_Syntax.vars = uu____10685;_},uu____10686,uu____10687))::uu____10688
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10695  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____10696)::uu____10697 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10708  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____10709 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10712  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____10716  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____10741 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____10741
                         | FStar_Util.Inr c ->
                             let uu____10755 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____10755
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____10778 =
                               let uu____10779 =
                                 let uu____10806 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____10806, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____10779
                                in
                             mk uu____10778 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____10841 ->
                           let uu____10842 =
                             let uu____10843 =
                               let uu____10844 =
                                 let uu____10871 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____10871, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____10844
                                in
                             mk uu____10843 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____10842))))
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
                   let uu___303_10948 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___304_10951 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___304_10951.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___304_10951.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___304_10951.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___304_10951.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___304_10951.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___304_10951.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___304_10951.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___304_10951.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___304_10951.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___304_10951.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___304_10951.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___304_10951.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___304_10951.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___304_10951.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___304_10951.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___304_10951.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___304_10951.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___304_10951.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___304_10951.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___304_10951.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___304_10951.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___304_10951.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___304_10951.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___304_10951.FStar_TypeChecker_Cfg.nbe_step)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___303_10948.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___303_10948.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___303_10948.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___303_10948.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___303_10948.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___303_10948.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___303_10948.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___303_10948.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____10987 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____10987 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___305_11007 = cfg  in
                               let uu____11008 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___305_11007.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____11008;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___305_11007.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___305_11007.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___305_11007.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___305_11007.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___305_11007.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___305_11007.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___305_11007.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____11015 =
                                 let uu____11016 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____11016  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____11015
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___306_11019 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___306_11019.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___306_11019.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___306_11019.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___306_11019.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____11020 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____11020
           | FStar_Syntax_Syntax.Tm_let
               ((uu____11031,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____11032;
                               FStar_Syntax_Syntax.lbunivs = uu____11033;
                               FStar_Syntax_Syntax.lbtyp = uu____11034;
                               FStar_Syntax_Syntax.lbeff = uu____11035;
                               FStar_Syntax_Syntax.lbdef = uu____11036;
                               FStar_Syntax_Syntax.lbattrs = uu____11037;
                               FStar_Syntax_Syntax.lbpos = uu____11038;_}::uu____11039),uu____11040)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name
                   cfg.FStar_TypeChecker_Cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____11080 =
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
               if uu____11080
               then
                 let binder =
                   let uu____11082 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____11082  in
                 let env1 =
                   let uu____11092 =
                     let uu____11099 =
                       let uu____11100 =
                         let uu____11131 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____11131,
                           false)
                          in
                       Clos uu____11100  in
                     ((FStar_Pervasives_Native.Some binder), uu____11099)  in
                   uu____11092 :: env  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____11226  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                 then
                   (FStar_TypeChecker_Cfg.log cfg
                      (fun uu____11230  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____11231 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____11231))
                 else
                   (let uu____11233 =
                      let uu____11238 =
                        let uu____11239 =
                          let uu____11246 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____11246
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____11239]  in
                      FStar_Syntax_Subst.open_term uu____11238 body  in
                    match uu____11233 with
                    | (bs,body1) ->
                        (FStar_TypeChecker_Cfg.log cfg
                           (fun uu____11273  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____11281 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____11281  in
                            FStar_Util.Inl
                              (let uu___307_11297 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___307_11297.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___307_11297.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____11300  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___308_11302 = lb  in
                             let uu____11303 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___308_11302.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___308_11302.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____11303;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___308_11302.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___308_11302.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11332  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___309_11357 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps =
                                 (uu___309_11357.FStar_TypeChecker_Cfg.steps);
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___309_11357.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___309_11357.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 (uu___309_11357.FStar_TypeChecker_Cfg.delta_level);
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___309_11357.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong = true;
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___309_11357.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___309_11357.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___309_11357.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           FStar_TypeChecker_Cfg.log cfg1
                             (fun uu____11360  ->
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
               let uu____11377 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____11377 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____11413 =
                               let uu___310_11414 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___310_11414.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___310_11414.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____11413  in
                           let uu____11415 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____11415 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____11441 =
                                   FStar_List.map (fun uu____11457  -> dummy)
                                     lbs1
                                    in
                                 let uu____11458 =
                                   let uu____11467 =
                                     FStar_List.map
                                       (fun uu____11489  -> dummy) xs1
                                      in
                                   FStar_List.append uu____11467 env  in
                                 FStar_List.append uu____11441 uu____11458
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____11515 =
                                       let uu___311_11516 = rc  in
                                       let uu____11517 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___311_11516.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____11517;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___311_11516.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____11515
                                 | uu____11526 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___312_11532 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___312_11532.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___312_11532.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___312_11532.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___312_11532.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____11542 =
                        FStar_List.map (fun uu____11558  -> dummy) lbs2  in
                      FStar_List.append uu____11542 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____11566 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____11566 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___313_11582 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___313_11582.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___313_11582.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
               ->
               let uu____11611 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____11611
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____11630 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____11706  ->
                        match uu____11706 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___314_11827 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___314_11827.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___314_11827.FStar_Syntax_Syntax.sort)
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
               (match uu____11630 with
                | (rec_env,memos,uu____12054) ->
                    let uu____12107 =
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
                             let uu____12418 =
                               let uu____12425 =
                                 let uu____12426 =
                                   let uu____12457 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____12457, false)
                                    in
                                 Clos uu____12426  in
                               (FStar_Pervasives_Native.None, uu____12425)
                                in
                             uu____12418 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____12561  ->
                     let uu____12562 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____12562);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____12584 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____12586::uu____12587 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____12592) ->
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
                             | uu____12619 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____12635 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____12635
                              | uu____12648 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____12654 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____12678 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____12692 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____12705 =
                        let uu____12706 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____12707 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____12706 uu____12707
                         in
                      failwith uu____12705
                    else
                      (let uu____12709 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____12709)
                | uu____12710 -> norm cfg env stack t2))

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
              let uu____12719 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____12719 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____12733  ->
                        let uu____12734 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____12734);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____12745  ->
                        let uu____12746 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____12747 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____12746 uu____12747);
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
                      | (UnivArgs (us',uu____12760))::stack1 ->
                          ((let uu____12769 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____12769
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____12773 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____12773) us'
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
                      | uu____12806 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____12809 ->
                          let uu____12812 =
                            let uu____12813 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____12813
                             in
                          failwith uu____12812
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
                  let uu___315_12837 = cfg  in
                  let uu____12838 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____12838;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___315_12837.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___315_12837.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___315_12837.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___315_12837.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___315_12837.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___315_12837.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___315_12837.FStar_TypeChecker_Cfg.reifying)
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
                  (fun uu____12873  ->
                     let uu____12874 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____12875 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____12874
                       uu____12875);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____12877 =
                   let uu____12878 = FStar_Syntax_Subst.compress head3  in
                   uu____12878.FStar_Syntax_Syntax.n  in
                 match uu____12877 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____12896 =
                         FStar_TypeChecker_Env.norm_eff_name
                           cfg.FStar_TypeChecker_Cfg.tcenv m
                          in
                       FStar_TypeChecker_Env.get_effect_decl
                         cfg.FStar_TypeChecker_Cfg.tcenv uu____12896
                        in
                     let uu____12897 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____12897 with
                      | (uu____12898,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____12908 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____12918 =
                                   let uu____12919 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____12919.FStar_Syntax_Syntax.n  in
                                 match uu____12918 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____12925,uu____12926))
                                     ->
                                     let uu____12935 =
                                       let uu____12936 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____12936.FStar_Syntax_Syntax.n  in
                                     (match uu____12935 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____12942,msrc,uu____12944))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____12953 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____12953
                                      | uu____12954 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____12955 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____12956 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____12956 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___316_12961 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___316_12961.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___316_12961.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___316_12961.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___316_12961.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___316_12961.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____12962 = FStar_List.tl stack  in
                                    let uu____12963 =
                                      let uu____12964 =
                                        let uu____12971 =
                                          let uu____12972 =
                                            let uu____12985 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____12985)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____12972
                                           in
                                        FStar_Syntax_Syntax.mk uu____12971
                                         in
                                      uu____12964
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____12962 uu____12963
                                | FStar_Pervasives_Native.None  ->
                                    let uu____13001 =
                                      let uu____13002 = is_return body  in
                                      match uu____13002 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____13006;
                                            FStar_Syntax_Syntax.vars =
                                              uu____13007;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____13010 -> false  in
                                    if uu____13001
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
                                         let uu____13031 =
                                           let uu____13038 =
                                             let uu____13039 =
                                               let uu____13058 =
                                                 let uu____13067 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____13067]  in
                                               (uu____13058, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____13039
                                              in
                                           FStar_Syntax_Syntax.mk uu____13038
                                            in
                                         uu____13031
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____13109 =
                                           let uu____13110 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____13110.FStar_Syntax_Syntax.n
                                            in
                                         match uu____13109 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____13116::uu____13117::[])
                                             ->
                                             let uu____13122 =
                                               let uu____13129 =
                                                 let uu____13130 =
                                                   let uu____13137 =
                                                     let uu____13138 =
                                                       let uu____13139 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.FStar_TypeChecker_Cfg.tcenv
                                                         uu____13139
                                                        in
                                                     let uu____13140 =
                                                       let uu____13143 =
                                                         let uu____13144 =
                                                           close1 t  in
                                                         (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.FStar_TypeChecker_Cfg.tcenv
                                                           uu____13144
                                                          in
                                                       [uu____13143]  in
                                                     uu____13138 ::
                                                       uu____13140
                                                      in
                                                   (bind1, uu____13137)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____13130
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____13129
                                                in
                                             uu____13122
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____13150 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____13164 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____13164
                                         then
                                           let uu____13175 =
                                             let uu____13184 =
                                               FStar_TypeChecker_Cfg.embed_simple
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____13184
                                              in
                                           let uu____13185 =
                                             let uu____13196 =
                                               let uu____13205 =
                                                 FStar_TypeChecker_Cfg.embed_simple
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____13205
                                                in
                                             [uu____13196]  in
                                           uu____13175 :: uu____13185
                                         else []  in
                                       let reified =
                                         let uu____13242 =
                                           let uu____13249 =
                                             let uu____13250 =
                                               let uu____13267 =
                                                 let uu____13278 =
                                                   let uu____13289 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____13298 =
                                                     let uu____13309 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____13309]  in
                                                   uu____13289 :: uu____13298
                                                    in
                                                 let uu____13342 =
                                                   let uu____13353 =
                                                     let uu____13364 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____13373 =
                                                       let uu____13384 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____13393 =
                                                         let uu____13404 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____13413 =
                                                           let uu____13424 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____13424]  in
                                                         uu____13404 ::
                                                           uu____13413
                                                          in
                                                       uu____13384 ::
                                                         uu____13393
                                                        in
                                                     uu____13364 ::
                                                       uu____13373
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____13353
                                                    in
                                                 FStar_List.append
                                                   uu____13278 uu____13342
                                                  in
                                               (bind_inst, uu____13267)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____13250
                                              in
                                           FStar_Syntax_Syntax.mk uu____13249
                                            in
                                         uu____13242
                                           FStar_Pervasives_Native.None rng
                                          in
                                       FStar_TypeChecker_Cfg.log cfg
                                         (fun uu____13508  ->
                                            let uu____13509 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____13510 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____13509 uu____13510);
                                       (let uu____13511 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____13511 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let maybe_unfold_action head4 =
                       let maybe_extract_fv t1 =
                         let t2 =
                           let uu____13565 =
                             let uu____13566 = FStar_Syntax_Subst.compress t1
                                in
                             uu____13566.FStar_Syntax_Syntax.n  in
                           match uu____13565 with
                           | FStar_Syntax_Syntax.Tm_uinst (t2,uu____13570) ->
                               t2
                           | uu____13575 -> head4  in
                         let uu____13576 =
                           let uu____13577 = FStar_Syntax_Subst.compress t2
                              in
                           uu____13577.FStar_Syntax_Syntax.n  in
                         match uu____13576 with
                         | FStar_Syntax_Syntax.Tm_fvar x ->
                             FStar_Pervasives_Native.Some x
                         | uu____13583 -> FStar_Pervasives_Native.None  in
                       let uu____13584 = maybe_extract_fv head4  in
                       match uu____13584 with
                       | FStar_Pervasives_Native.Some x when
                           let uu____13594 = FStar_Syntax_Syntax.lid_of_fv x
                              in
                           FStar_TypeChecker_Env.is_action
                             cfg.FStar_TypeChecker_Cfg.tcenv uu____13594
                           ->
                           let head5 = norm cfg env [] head4  in
                           let action_unfolded =
                             let uu____13599 = maybe_extract_fv head5  in
                             match uu____13599 with
                             | FStar_Pervasives_Native.Some uu____13604 ->
                                 FStar_Pervasives_Native.Some true
                             | uu____13605 ->
                                 FStar_Pervasives_Native.Some false
                              in
                           (head5, action_unfolded)
                       | uu____13610 -> (head4, FStar_Pervasives_Native.None)
                        in
                     ((let uu____13616 = FStar_Options.defensive ()  in
                       if uu____13616
                       then
                         let is_arg_impure uu____13628 =
                           match uu____13628 with
                           | (e,q) ->
                               let uu____13641 =
                                 let uu____13642 =
                                   FStar_Syntax_Subst.compress e  in
                                 uu____13642.FStar_Syntax_Syntax.n  in
                               (match uu____13641 with
                                | FStar_Syntax_Syntax.Tm_meta
                                    (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                     (m1,m2,t'))
                                    ->
                                    let uu____13657 =
                                      FStar_Syntax_Util.is_pure_effect m1  in
                                    Prims.op_Negation uu____13657
                                | uu____13658 -> false)
                            in
                         let uu____13659 =
                           let uu____13660 =
                             let uu____13671 =
                               FStar_Syntax_Syntax.as_arg head_app  in
                             uu____13671 :: args  in
                           FStar_Util.for_some is_arg_impure uu____13660  in
                         (if uu____13659
                          then
                            let uu____13696 =
                              let uu____13701 =
                                let uu____13702 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____13702
                                 in
                              (FStar_Errors.Warning_Defensive, uu____13701)
                               in
                            FStar_Errors.log_issue
                              head3.FStar_Syntax_Syntax.pos uu____13696
                          else ())
                       else ());
                      (let uu____13705 = maybe_unfold_action head_app  in
                       match uu____13705 with
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
                              (fun uu____13750  ->
                                 let uu____13751 =
                                   FStar_Syntax_Print.term_to_string head0
                                    in
                                 let uu____13752 =
                                   FStar_Syntax_Print.term_to_string body1
                                    in
                                 FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                   uu____13751 uu____13752);
                            (let uu____13753 = FStar_List.tl stack  in
                             norm cfg env uu____13753 body1))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____13755) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____13779 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____13779  in
                     (FStar_TypeChecker_Cfg.log cfg
                        (fun uu____13783  ->
                           let uu____13784 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____13784);
                      (let uu____13785 = FStar_List.tl stack  in
                       norm cfg env uu____13785 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____13906  ->
                               match uu____13906 with
                               | (pat,wopt,tm) ->
                                   let uu____13954 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____13954)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____13986 = FStar_List.tl stack  in
                     norm cfg env uu____13986 tm
                 | uu____13987 -> fallback ())

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
              (fun uu____14001  ->
                 let uu____14002 = FStar_Ident.string_of_lid msrc  in
                 let uu____14003 = FStar_Ident.string_of_lid mtgt  in
                 let uu____14004 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____14002
                   uu____14003 uu____14004);
            (let uu____14005 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____14005
             then
               let ed =
                 let uu____14007 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____14007  in
               let uu____14008 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____14008 with
               | (uu____14009,return_repr) ->
                   let return_inst =
                     let uu____14022 =
                       let uu____14023 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____14023.FStar_Syntax_Syntax.n  in
                     match uu____14022 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____14029::[]) ->
                         let uu____14034 =
                           let uu____14041 =
                             let uu____14042 =
                               let uu____14049 =
                                 let uu____14050 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____14050]  in
                               (return_tm, uu____14049)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____14042  in
                           FStar_Syntax_Syntax.mk uu____14041  in
                         uu____14034 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____14056 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____14059 =
                     let uu____14066 =
                       let uu____14067 =
                         let uu____14084 =
                           let uu____14095 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____14104 =
                             let uu____14115 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____14115]  in
                           uu____14095 :: uu____14104  in
                         (return_inst, uu____14084)  in
                       FStar_Syntax_Syntax.Tm_app uu____14067  in
                     FStar_Syntax_Syntax.mk uu____14066  in
                   uu____14059 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____14164 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____14164 with
                | FStar_Pervasives_Native.None  ->
                    let uu____14167 =
                      let uu____14168 = FStar_Ident.text_of_lid msrc  in
                      let uu____14169 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____14168 uu____14169
                       in
                    failwith uu____14167
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14170;
                      FStar_TypeChecker_Env.mtarget = uu____14171;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14172;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____14194 =
                      let uu____14195 = FStar_Ident.text_of_lid msrc  in
                      let uu____14196 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____14195 uu____14196
                       in
                    failwith uu____14194
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14197;
                      FStar_TypeChecker_Env.mtarget = uu____14198;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14199;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____14234 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____14235 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____14234 t FStar_Syntax_Syntax.tun uu____14235))

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
                (fun uu____14305  ->
                   match uu____14305 with
                   | (a,imp) ->
                       let uu____14324 = norm cfg env [] a  in
                       (uu____14324, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____14334  ->
             let uu____14335 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____14336 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____14335 uu____14336);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____14360 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____14360
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___317_14363 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___317_14363.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___317_14363.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____14385 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____14385
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___318_14388 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___318_14388.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___318_14388.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____14433  ->
                      match uu____14433 with
                      | (a,i) ->
                          let uu____14452 = norm cfg env [] a  in
                          (uu____14452, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___262_14474  ->
                       match uu___262_14474 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____14478 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____14478
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___319_14486 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___320_14489 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___320_14489.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___319_14486.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___319_14486.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun uu____14492  ->
        match uu____14492 with
        | (x,imp) ->
            let uu____14499 =
              let uu___321_14500 = x  in
              let uu____14501 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___321_14500.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___321_14500.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____14501
              }  in
            (uu____14499, imp)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____14509 =
          FStar_List.fold_left
            (fun uu____14543  ->
               fun b  ->
                 match uu____14543 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____14509 with | (nbs,uu____14623) -> FStar_List.rev nbs

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
            let uu____14655 =
              let uu___322_14656 = rc  in
              let uu____14657 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___322_14656.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____14657;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___322_14656.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____14655
        | uu____14666 -> lopt

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
            (let uu____14675 = FStar_Syntax_Print.term_to_string tm  in
             let uu____14676 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____14675 uu____14676)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___263_14680  ->
      match uu___263_14680 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____14693 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____14693 with
           | FStar_Pervasives_Native.Some (t,uu____14701) -> t
           | FStar_Pervasives_Native.None  ->
               let uu____14710 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____14710)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____14718 = norm_cb cfg  in
            reduce_primops uu____14718 cfg env tm  in
          let uu____14725 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____14725
          then tm1
          else
            (let w t =
               let uu___323_14739 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___323_14739.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___323_14739.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____14750 =
                 let uu____14751 = FStar_Syntax_Util.unmeta t  in
                 uu____14751.FStar_Syntax_Syntax.n  in
               match uu____14750 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____14758 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____14819)::args1,(bv,uu____14822)::bs1) ->
                   let uu____14876 =
                     let uu____14877 = FStar_Syntax_Subst.compress t  in
                     uu____14877.FStar_Syntax_Syntax.n  in
                   (match uu____14876 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____14881 -> false)
               | ([],[]) -> true
               | (uu____14910,uu____14911) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____14960 = FStar_Syntax_Print.term_to_string t  in
                  let uu____14961 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____14960
                    uu____14961)
               else ();
               (let uu____14963 = FStar_Syntax_Util.head_and_args' t  in
                match uu____14963 with
                | (hd1,args) ->
                    let uu____15002 =
                      let uu____15003 = FStar_Syntax_Subst.compress hd1  in
                      uu____15003.FStar_Syntax_Syntax.n  in
                    (match uu____15002 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____15010 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____15011 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____15012 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____15010 uu____15011 uu____15012)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____15014 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____15031 = FStar_Syntax_Print.term_to_string t  in
                  let uu____15032 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____15031
                    uu____15032)
               else ();
               (let uu____15034 = FStar_Syntax_Util.is_squash t  in
                match uu____15034 with
                | FStar_Pervasives_Native.Some (uu____15045,t') ->
                    is_applied bs t'
                | uu____15057 ->
                    let uu____15066 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____15066 with
                     | FStar_Pervasives_Native.Some (uu____15077,t') ->
                         is_applied bs t'
                     | uu____15089 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____15113 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____15113 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____15120)::(q,uu____15122)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____15164 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____15165 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____15164 uu____15165)
                    else ();
                    (let uu____15167 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____15167 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____15172 =
                           let uu____15173 = FStar_Syntax_Subst.compress p
                              in
                           uu____15173.FStar_Syntax_Syntax.n  in
                         (match uu____15172 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____15181 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____15181))
                          | uu____15184 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____15187)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____15212 =
                           let uu____15213 = FStar_Syntax_Subst.compress p1
                              in
                           uu____15213.FStar_Syntax_Syntax.n  in
                         (match uu____15212 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____15221 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____15221))
                          | uu____15224 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____15228 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____15228 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____15233 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____15233 with
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
                                     let uu____15244 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____15244))
                               | uu____15247 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____15252)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____15277 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____15277 with
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
                                     let uu____15288 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____15288))
                               | uu____15291 -> FStar_Pervasives_Native.None)
                          | uu____15294 -> FStar_Pervasives_Native.None)
                     | uu____15297 -> FStar_Pervasives_Native.None))
               | uu____15300 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____15313 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____15313 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____15319)::[],uu____15320,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____15339 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____15340 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____15339
                         uu____15340)
                    else ();
                    is_quantified_const bv phi')
               | uu____15342 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____15355 =
                 let uu____15356 = FStar_Syntax_Subst.compress phi  in
                 uu____15356.FStar_Syntax_Syntax.n  in
               match uu____15355 with
               | FStar_Syntax_Syntax.Tm_match (uu____15361,br::brs) ->
                   let uu____15428 = br  in
                   (match uu____15428 with
                    | (uu____15445,uu____15446,e) ->
                        let r =
                          let uu____15467 = simp_t e  in
                          match uu____15467 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____15473 =
                                FStar_List.for_all
                                  (fun uu____15491  ->
                                     match uu____15491 with
                                     | (uu____15504,uu____15505,e') ->
                                         let uu____15519 = simp_t e'  in
                                         uu____15519 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____15473
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____15527 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____15536 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____15536
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____15571 =
                 match uu____15571 with
                 | (t1,q) ->
                     let uu____15592 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____15592 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____15624 -> (t1, q))
                  in
               let uu____15637 = FStar_Syntax_Util.head_and_args t  in
               match uu____15637 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____15715 =
                 let uu____15716 = FStar_Syntax_Util.unmeta ty  in
                 uu____15716.FStar_Syntax_Syntax.n  in
               match uu____15715 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____15720) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____15725,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____15749 -> false  in
             let simplify1 arg =
               let uu____15780 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____15780, arg)  in
             let uu____15793 = is_forall_const tm1  in
             match uu____15793 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____15798 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____15799 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____15798
                       uu____15799)
                  else ();
                  (let uu____15801 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____15801))
             | FStar_Pervasives_Native.None  ->
                 let uu____15802 =
                   let uu____15803 = FStar_Syntax_Subst.compress tm1  in
                   uu____15803.FStar_Syntax_Syntax.n  in
                 (match uu____15802 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____15807;
                              FStar_Syntax_Syntax.vars = uu____15808;_},uu____15809);
                         FStar_Syntax_Syntax.pos = uu____15810;
                         FStar_Syntax_Syntax.vars = uu____15811;_},args)
                      ->
                      let uu____15841 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____15841
                      then
                        let uu____15842 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____15842 with
                         | (FStar_Pervasives_Native.Some (true ),uu____15897)::
                             (uu____15898,(arg,uu____15900))::[] ->
                             maybe_auto_squash arg
                         | (uu____15965,(arg,uu____15967))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____15968)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____16033)::uu____16034::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____16097::(FStar_Pervasives_Native.Some (false
                                         ),uu____16098)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____16161 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____16177 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____16177
                         then
                           let uu____16178 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____16178 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____16233)::uu____16234::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____16297::(FStar_Pervasives_Native.Some (true
                                           ),uu____16298)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____16361)::(uu____16362,(arg,uu____16364))::[]
                               -> maybe_auto_squash arg
                           | (uu____16429,(arg,uu____16431))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____16432)::[]
                               -> maybe_auto_squash arg
                           | uu____16497 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____16513 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____16513
                            then
                              let uu____16514 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____16514 with
                              | uu____16569::(FStar_Pervasives_Native.Some
                                              (true ),uu____16570)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____16633)::uu____16634::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____16697)::(uu____16698,(arg,uu____16700))::[]
                                  -> maybe_auto_squash arg
                              | (uu____16765,(p,uu____16767))::(uu____16768,
                                                                (q,uu____16770))::[]
                                  ->
                                  let uu____16835 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____16835
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____16837 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____16853 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____16853
                               then
                                 let uu____16854 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____16854 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16909)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____16910)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____16975)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____16976)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17041)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____17042)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17107)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17108)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____17173,(arg,uu____17175))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____17176)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17241)::(uu____17242,(arg,uu____17244))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____17309,(arg,uu____17311))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____17312)::[]
                                     ->
                                     let uu____17377 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17377
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17378)::(uu____17379,(arg,uu____17381))::[]
                                     ->
                                     let uu____17446 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17446
                                 | (uu____17447,(p,uu____17449))::(uu____17450,
                                                                   (q,uu____17452))::[]
                                     ->
                                     let uu____17517 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____17517
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____17519 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____17535 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____17535
                                  then
                                    let uu____17536 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____17536 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____17591)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____17630)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____17669 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____17685 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____17685
                                     then
                                       match args with
                                       | (t,uu____17687)::[] ->
                                           let uu____17712 =
                                             let uu____17713 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17713.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17712 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17716::[],body,uu____17718)
                                                ->
                                                let uu____17753 = simp_t body
                                                   in
                                                (match uu____17753 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____17756 -> tm1)
                                            | uu____17759 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____17761))::(t,uu____17763)::[]
                                           ->
                                           let uu____17802 =
                                             let uu____17803 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17803.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17802 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17806::[],body,uu____17808)
                                                ->
                                                let uu____17843 = simp_t body
                                                   in
                                                (match uu____17843 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____17846 -> tm1)
                                            | uu____17849 -> tm1)
                                       | uu____17850 -> tm1
                                     else
                                       (let uu____17862 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____17862
                                        then
                                          match args with
                                          | (t,uu____17864)::[] ->
                                              let uu____17889 =
                                                let uu____17890 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17890.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17889 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17893::[],body,uu____17895)
                                                   ->
                                                   let uu____17930 =
                                                     simp_t body  in
                                                   (match uu____17930 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____17933 -> tm1)
                                               | uu____17936 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____17938))::(t,uu____17940)::[]
                                              ->
                                              let uu____17979 =
                                                let uu____17980 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17980.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17979 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17983::[],body,uu____17985)
                                                   ->
                                                   let uu____18020 =
                                                     simp_t body  in
                                                   (match uu____18020 with
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
                                                    | uu____18023 -> tm1)
                                               | uu____18026 -> tm1)
                                          | uu____18027 -> tm1
                                        else
                                          (let uu____18039 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____18039
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18040;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18041;_},uu____18042)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18067;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18068;_},uu____18069)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____18094 -> tm1
                                           else
                                             (let uu____18106 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____18106 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____18126 ->
                                                  let uu____18135 =
                                                    let uu____18142 =
                                                      norm_cb cfg  in
                                                    reduce_equality
                                                      uu____18142 cfg env
                                                     in
                                                  uu____18135 tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____18150;
                         FStar_Syntax_Syntax.vars = uu____18151;_},args)
                      ->
                      let uu____18177 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18177
                      then
                        let uu____18178 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18178 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18233)::
                             (uu____18234,(arg,uu____18236))::[] ->
                             maybe_auto_squash arg
                         | (uu____18301,(arg,uu____18303))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18304)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18369)::uu____18370::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18433::(FStar_Pervasives_Native.Some (false
                                         ),uu____18434)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18497 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18513 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18513
                         then
                           let uu____18514 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18514 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18569)::uu____18570::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18633::(FStar_Pervasives_Native.Some (true
                                           ),uu____18634)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18697)::(uu____18698,(arg,uu____18700))::[]
                               -> maybe_auto_squash arg
                           | (uu____18765,(arg,uu____18767))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18768)::[]
                               -> maybe_auto_squash arg
                           | uu____18833 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18849 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____18849
                            then
                              let uu____18850 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____18850 with
                              | uu____18905::(FStar_Pervasives_Native.Some
                                              (true ),uu____18906)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____18969)::uu____18970::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19033)::(uu____19034,(arg,uu____19036))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19101,(p,uu____19103))::(uu____19104,
                                                                (q,uu____19106))::[]
                                  ->
                                  let uu____19171 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19171
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19173 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19189 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19189
                               then
                                 let uu____19190 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19190 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19245)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19246)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19311)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19312)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19377)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19378)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19443)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19444)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19509,(arg,uu____19511))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19512)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19577)::(uu____19578,(arg,uu____19580))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19645,(arg,uu____19647))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19648)::[]
                                     ->
                                     let uu____19713 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19713
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19714)::(uu____19715,(arg,uu____19717))::[]
                                     ->
                                     let uu____19782 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19782
                                 | (uu____19783,(p,uu____19785))::(uu____19786,
                                                                   (q,uu____19788))::[]
                                     ->
                                     let uu____19853 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19853
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19855 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19871 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19871
                                  then
                                    let uu____19872 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19872 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19927)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19966)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20005 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20021 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____20021
                                     then
                                       match args with
                                       | (t,uu____20023)::[] ->
                                           let uu____20048 =
                                             let uu____20049 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20049.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20048 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20052::[],body,uu____20054)
                                                ->
                                                let uu____20089 = simp_t body
                                                   in
                                                (match uu____20089 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20092 -> tm1)
                                            | uu____20095 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20097))::(t,uu____20099)::[]
                                           ->
                                           let uu____20138 =
                                             let uu____20139 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20139.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20138 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20142::[],body,uu____20144)
                                                ->
                                                let uu____20179 = simp_t body
                                                   in
                                                (match uu____20179 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20182 -> tm1)
                                            | uu____20185 -> tm1)
                                       | uu____20186 -> tm1
                                     else
                                       (let uu____20198 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20198
                                        then
                                          match args with
                                          | (t,uu____20200)::[] ->
                                              let uu____20225 =
                                                let uu____20226 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20226.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20225 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20229::[],body,uu____20231)
                                                   ->
                                                   let uu____20266 =
                                                     simp_t body  in
                                                   (match uu____20266 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20269 -> tm1)
                                               | uu____20272 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20274))::(t,uu____20276)::[]
                                              ->
                                              let uu____20315 =
                                                let uu____20316 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20316.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20315 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20319::[],body,uu____20321)
                                                   ->
                                                   let uu____20356 =
                                                     simp_t body  in
                                                   (match uu____20356 with
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
                                                    | uu____20359 -> tm1)
                                               | uu____20362 -> tm1)
                                          | uu____20363 -> tm1
                                        else
                                          (let uu____20375 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20375
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20376;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20377;_},uu____20378)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20403;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20404;_},uu____20405)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20430 -> tm1
                                           else
                                             (let uu____20442 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20442 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20462 ->
                                                  let uu____20471 =
                                                    let uu____20478 =
                                                      norm_cb cfg  in
                                                    reduce_equality
                                                      uu____20478 cfg env
                                                     in
                                                  uu____20471 tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____20491 = simp_t t  in
                      (match uu____20491 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____20494 ->
                      let uu____20517 = is_const_match tm1  in
                      (match uu____20517 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____20520 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____20530  ->
               (let uu____20532 = FStar_Syntax_Print.tag_of_term t  in
                let uu____20533 = FStar_Syntax_Print.term_to_string t  in
                let uu____20534 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____20541 =
                  let uu____20542 =
                    let uu____20545 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____20545
                     in
                  stack_to_string uu____20542  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____20532 uu____20533 uu____20534 uu____20541);
               (let uu____20568 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____20568
                then
                  let uu____20569 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____20569 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____20576 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____20577 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____20578 =
                          let uu____20579 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____20579
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____20576
                          uu____20577 uu____20578);
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
                   let uu____20597 =
                     let uu____20598 =
                       let uu____20599 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____20599  in
                     FStar_Util.string_of_int uu____20598  in
                   let uu____20604 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____20605 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____20597 uu____20604 uu____20605)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____20611,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                FStar_TypeChecker_Cfg.log cfg
                  (fun uu____20662  ->
                     let uu____20663 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____20663);
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
               let uu____20701 =
                 let uu___324_20702 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___324_20702.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___324_20702.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____20701
           | (Arg (Univ uu____20705,uu____20706,uu____20707))::uu____20708 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____20711,uu____20712))::uu____20713 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____20728,uu____20729),aq,r))::stack1
               when
               let uu____20779 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____20779 ->
               let t2 =
                 let uu____20783 =
                   let uu____20788 =
                     let uu____20789 = closure_as_term cfg env_arg tm  in
                     (uu____20789, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____20788  in
                 uu____20783 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____20801),aq,r))::stack1 ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____20854  ->
                     let uu____20855 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____20855);
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
                  (let uu____20869 = FStar_ST.op_Bang m  in
                   match uu____20869 with
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
                   | FStar_Pervasives_Native.Some (uu____21010,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____21065 =
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____21069  ->
                      let uu____21070 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____21070);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____21078 =
                 let uu____21079 = FStar_Syntax_Subst.compress t1  in
                 uu____21079.FStar_Syntax_Syntax.n  in
               (match uu____21078 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____21106 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____21106  in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____21110  ->
                          let uu____21111 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____21111);
                     (let uu____21112 = FStar_List.tl stack  in
                      norm cfg env1 uu____21112 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____21113);
                       FStar_Syntax_Syntax.pos = uu____21114;
                       FStar_Syntax_Syntax.vars = uu____21115;_},(e,uu____21117)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____21156 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                    ->
                    let uu____21173 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____21173 with
                     | (hd1,args) ->
                         let uu____21216 =
                           let uu____21217 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____21217.FStar_Syntax_Syntax.n  in
                         (match uu____21216 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____21221 =
                                FStar_TypeChecker_Cfg.find_prim_step cfg fv
                                 in
                              (match uu____21221 with
                               | FStar_Pervasives_Native.Some
                                   {
                                     FStar_TypeChecker_Cfg.name = uu____21224;
                                     FStar_TypeChecker_Cfg.arity =
                                       uu____21225;
                                     FStar_TypeChecker_Cfg.univ_arity =
                                       uu____21226;
                                     FStar_TypeChecker_Cfg.auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     FStar_TypeChecker_Cfg.strong_reduction_ok
                                       = uu____21228;
                                     FStar_TypeChecker_Cfg.requires_binder_substitution
                                       = uu____21229;
                                     FStar_TypeChecker_Cfg.interpretation =
                                       uu____21230;
                                     FStar_TypeChecker_Cfg.interpretation_nbe
                                       = uu____21231;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____21258 -> fallback " (3)" ())
                          | uu____21261 -> fallback " (4)" ()))
                | uu____21262 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (FStar_TypeChecker_Cfg.log cfg1
                  (fun uu____21287  ->
                     let uu____21288 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____21288);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____21297 =
                   FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____21302  ->
                        let uu____21303 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____21304 =
                          let uu____21305 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____21332  ->
                                    match uu____21332 with
                                    | (p,uu____21342,uu____21343) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____21305
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____21303 uu____21304);
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
                             (fun uu___264_21360  ->
                                match uu___264_21360 with
                                | FStar_TypeChecker_Env.InliningDelta  ->
                                    true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____21361 -> false))
                         in
                      let steps =
                        let uu___325_21363 = cfg1.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___325_21363.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___325_21363.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta = false;
                          FStar_TypeChecker_Cfg.weak =
                            (uu___325_21363.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___325_21363.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___325_21363.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___325_21363.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___325_21363.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_tac = false;
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___325_21363.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___325_21363.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___325_21363.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___325_21363.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___325_21363.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___325_21363.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___325_21363.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___325_21363.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___325_21363.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___325_21363.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___325_21363.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___325_21363.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___325_21363.FStar_TypeChecker_Cfg.nbe_step)
                        }  in
                      let uu___326_21368 = cfg1  in
                      {
                        FStar_TypeChecker_Cfg.steps = steps;
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___326_21368.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___326_21368.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level = new_delta;
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___326_21368.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong = true;
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___326_21368.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___326_21368.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying =
                          (uu___326_21368.FStar_TypeChecker_Cfg.reifying)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____21440 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____21469 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____21553  ->
                                    fun uu____21554  ->
                                      match (uu____21553, uu____21554) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____21693 = norm_pat env3 p1
                                             in
                                          (match uu____21693 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____21469 with
                           | (pats1,env3) ->
                               ((let uu___327_21855 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___327_21855.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___328_21874 = x  in
                            let uu____21875 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___328_21874.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___328_21874.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21875
                            }  in
                          ((let uu___329_21889 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___329_21889.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___330_21900 = x  in
                            let uu____21901 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___330_21900.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___330_21900.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21901
                            }  in
                          ((let uu___331_21915 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___331_21915.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___332_21931 = x  in
                            let uu____21932 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___332_21931.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___332_21931.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21932
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___333_21947 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___333_21947.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____21991 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____22021 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____22021 with
                                  | (p,wopt,e) ->
                                      let uu____22041 = norm_pat env1 p  in
                                      (match uu____22041 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____22096 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____22096
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____22113 =
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
                      if uu____22113
                      then
                        norm
                          (let uu___334_22118 = cfg1  in
                           {
                             FStar_TypeChecker_Cfg.steps =
                               (let uu___335_22121 =
                                  cfg1.FStar_TypeChecker_Cfg.steps  in
                                {
                                  FStar_TypeChecker_Cfg.beta =
                                    (uu___335_22121.FStar_TypeChecker_Cfg.beta);
                                  FStar_TypeChecker_Cfg.iota =
                                    (uu___335_22121.FStar_TypeChecker_Cfg.iota);
                                  FStar_TypeChecker_Cfg.zeta =
                                    (uu___335_22121.FStar_TypeChecker_Cfg.zeta);
                                  FStar_TypeChecker_Cfg.weak =
                                    (uu___335_22121.FStar_TypeChecker_Cfg.weak);
                                  FStar_TypeChecker_Cfg.hnf =
                                    (uu___335_22121.FStar_TypeChecker_Cfg.hnf);
                                  FStar_TypeChecker_Cfg.primops =
                                    (uu___335_22121.FStar_TypeChecker_Cfg.primops);
                                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                    =
                                    (uu___335_22121.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                  FStar_TypeChecker_Cfg.unfold_until =
                                    (uu___335_22121.FStar_TypeChecker_Cfg.unfold_until);
                                  FStar_TypeChecker_Cfg.unfold_only =
                                    (uu___335_22121.FStar_TypeChecker_Cfg.unfold_only);
                                  FStar_TypeChecker_Cfg.unfold_fully =
                                    (uu___335_22121.FStar_TypeChecker_Cfg.unfold_fully);
                                  FStar_TypeChecker_Cfg.unfold_attr =
                                    (uu___335_22121.FStar_TypeChecker_Cfg.unfold_attr);
                                  FStar_TypeChecker_Cfg.unfold_tac =
                                    (uu___335_22121.FStar_TypeChecker_Cfg.unfold_tac);
                                  FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                    =
                                    (uu___335_22121.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                  FStar_TypeChecker_Cfg.simplify =
                                    (uu___335_22121.FStar_TypeChecker_Cfg.simplify);
                                  FStar_TypeChecker_Cfg.erase_universes =
                                    (uu___335_22121.FStar_TypeChecker_Cfg.erase_universes);
                                  FStar_TypeChecker_Cfg.allow_unbound_universes
                                    =
                                    (uu___335_22121.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                  FStar_TypeChecker_Cfg.reify_ =
                                    (uu___335_22121.FStar_TypeChecker_Cfg.reify_);
                                  FStar_TypeChecker_Cfg.compress_uvars =
                                    (uu___335_22121.FStar_TypeChecker_Cfg.compress_uvars);
                                  FStar_TypeChecker_Cfg.no_full_norm =
                                    (uu___335_22121.FStar_TypeChecker_Cfg.no_full_norm);
                                  FStar_TypeChecker_Cfg.check_no_uvars =
                                    (uu___335_22121.FStar_TypeChecker_Cfg.check_no_uvars);
                                  FStar_TypeChecker_Cfg.unmeta =
                                    (uu___335_22121.FStar_TypeChecker_Cfg.unmeta);
                                  FStar_TypeChecker_Cfg.unascribe =
                                    (uu___335_22121.FStar_TypeChecker_Cfg.unascribe);
                                  FStar_TypeChecker_Cfg.in_full_norm_request
                                    =
                                    (uu___335_22121.FStar_TypeChecker_Cfg.in_full_norm_request);
                                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                    = false;
                                  FStar_TypeChecker_Cfg.nbe_step =
                                    (uu___335_22121.FStar_TypeChecker_Cfg.nbe_step)
                                });
                             FStar_TypeChecker_Cfg.tcenv =
                               (uu___334_22118.FStar_TypeChecker_Cfg.tcenv);
                             FStar_TypeChecker_Cfg.debug =
                               (uu___334_22118.FStar_TypeChecker_Cfg.debug);
                             FStar_TypeChecker_Cfg.delta_level =
                               (uu___334_22118.FStar_TypeChecker_Cfg.delta_level);
                             FStar_TypeChecker_Cfg.primitive_steps =
                               (uu___334_22118.FStar_TypeChecker_Cfg.primitive_steps);
                             FStar_TypeChecker_Cfg.strong =
                               (uu___334_22118.FStar_TypeChecker_Cfg.strong);
                             FStar_TypeChecker_Cfg.memoize_lazy =
                               (uu___334_22118.FStar_TypeChecker_Cfg.memoize_lazy);
                             FStar_TypeChecker_Cfg.normalize_pure_lets =
                               (uu___334_22118.FStar_TypeChecker_Cfg.normalize_pure_lets);
                             FStar_TypeChecker_Cfg.reifying =
                               (uu___334_22118.FStar_TypeChecker_Cfg.reifying)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____22123 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____22123)
                    in
                 let rec is_cons head1 =
                   let uu____22148 =
                     let uu____22149 = FStar_Syntax_Subst.compress head1  in
                     uu____22149.FStar_Syntax_Syntax.n  in
                   match uu____22148 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____22153) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____22158 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____22159;
                         FStar_Syntax_Syntax.fv_delta = uu____22160;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____22161;
                         FStar_Syntax_Syntax.fv_delta = uu____22162;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____22163);_}
                       -> true
                   | uu____22170 -> false  in
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
                   let uu____22333 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____22333 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____22426 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____22465 ->
                                 let uu____22466 =
                                   let uu____22467 = is_cons head1  in
                                   Prims.op_Negation uu____22467  in
                                 FStar_Util.Inr uu____22466)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____22492 =
                              let uu____22493 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____22493.FStar_Syntax_Syntax.n  in
                            (match uu____22492 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____22511 ->
                                 let uu____22512 =
                                   let uu____22513 = is_cons head1  in
                                   Prims.op_Negation uu____22513  in
                                 FStar_Util.Inr uu____22512))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____22596)::rest_a,(p1,uu____22599)::rest_p) ->
                       let uu____22653 = matches_pat t2 p1  in
                       (match uu____22653 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____22702 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____22822 = matches_pat scrutinee1 p1  in
                       (match uu____22822 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (FStar_TypeChecker_Cfg.log cfg1
                               (fun uu____22862  ->
                                  let uu____22863 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____22864 =
                                    let uu____22865 =
                                      FStar_List.map
                                        (fun uu____22875  ->
                                           match uu____22875 with
                                           | (uu____22880,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____22865
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____22863 uu____22864);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____22912  ->
                                       match uu____22912 with
                                       | (bv,t2) ->
                                           let uu____22935 =
                                             let uu____22942 =
                                               let uu____22945 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____22945
                                                in
                                             let uu____22946 =
                                               let uu____22947 =
                                                 let uu____22978 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____22978, false)
                                                  in
                                               Clos uu____22947  in
                                             (uu____22942, uu____22946)  in
                                           uu____22935 :: env2) env1 s
                                 in
                              let uu____23091 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____23091)))
                    in
                 if
                   (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                 then
                   let uu____23092 = FStar_Syntax_Util.unlazy scrutinee  in
                   matches uu____23092 branches
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
            (fun uu____23122  ->
               let uu____23123 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____23123);
          (let uu____23124 = is_nbe_request s  in
           if uu____23124
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____23128  ->
                   let uu____23129 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____23129);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____23133  ->
                   let uu____23134 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____23134);
              (let r = nbe_eval c s t  in
               FStar_TypeChecker_Cfg.log_top c
                 (fun uu____23139  ->
                    let uu____23140 = FStar_Syntax_Print.term_to_string r  in
                    FStar_Util.print1 "}\nNormalization result = (%s)\n"
                      uu____23140);
               r))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____23145  ->
                   let uu____23146 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____23146);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____23150  ->
                   let uu____23151 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____23151);
              (let r = norm c [] [] t  in
               FStar_TypeChecker_Cfg.log_top c
                 (fun uu____23162  ->
                    let uu____23163 = FStar_Syntax_Print.term_to_string r  in
                    FStar_Util.print1 "}\nNormalization result = (%s)\n"
                      uu____23163);
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
        let uu____23194 = FStar_TypeChecker_Cfg.config s e  in
        norm_comp uu____23194 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____23211 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____23211 [] u
  
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
        let uu____23235 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____23235  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____23242 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___336_23261 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___336_23261.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___336_23261.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name
              cfg.FStar_TypeChecker_Cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____23268 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____23268
          then
            let ct1 =
              let uu____23270 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____23270 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____23277 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____23277
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___337_23281 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___337_23281.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___337_23281.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___337_23281.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev
                      cfg.FStar_TypeChecker_Cfg.tcenv c
                     in
                  let uu___338_23283 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___338_23283.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___338_23283.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___338_23283.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___338_23283.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___339_23284 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___339_23284.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___339_23284.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____23286 -> c
  
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
        let uu____23304 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____23304  in
      let uu____23311 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____23311
      then
        let uu____23312 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____23312 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____23318  ->
                 let uu____23319 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____23319)
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env t
        with
        | e ->
            ((let uu____23340 =
                let uu____23345 =
                  let uu____23346 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23346
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____23345)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____23340);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____23361 =
            FStar_TypeChecker_Cfg.config
              [FStar_TypeChecker_Env.AllowUnboundUniverses] env
             in
          norm_comp uu____23361 [] c
        with
        | e ->
            ((let uu____23374 =
                let uu____23379 =
                  let uu____23380 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23380
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____23379)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____23374);
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
                   let uu____23425 =
                     let uu____23426 =
                       let uu____23433 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____23433)  in
                     FStar_Syntax_Syntax.Tm_refine uu____23426  in
                   mk uu____23425 t01.FStar_Syntax_Syntax.pos
               | uu____23438 -> t2)
          | uu____23439 -> t2  in
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
        let uu____23518 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____23518 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____23555 ->
                 let uu____23564 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____23564 with
                  | (actuals,uu____23574,uu____23575) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____23593 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____23593 with
                         | (binders,args) ->
                             let uu____23604 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____23604
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
      | uu____23618 ->
          let uu____23619 = FStar_Syntax_Util.head_and_args t  in
          (match uu____23619 with
           | (head1,args) ->
               let uu____23662 =
                 let uu____23663 = FStar_Syntax_Subst.compress head1  in
                 uu____23663.FStar_Syntax_Syntax.n  in
               (match uu____23662 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____23684 =
                      let uu____23699 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____23699  in
                    (match uu____23684 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____23737 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___344_23745 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___344_23745.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___344_23745.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___344_23745.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___344_23745.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___344_23745.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___344_23745.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___344_23745.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___344_23745.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___344_23745.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___344_23745.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___344_23745.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___344_23745.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___344_23745.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___344_23745.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___344_23745.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___344_23745.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___344_23745.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___344_23745.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___344_23745.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___344_23745.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___344_23745.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___344_23745.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___344_23745.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___344_23745.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___344_23745.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___344_23745.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___344_23745.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___344_23745.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___344_23745.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___344_23745.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___344_23745.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___344_23745.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___344_23745.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___344_23745.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___344_23745.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___344_23745.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___344_23745.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___344_23745.FStar_TypeChecker_Env.dep_graph);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___344_23745.FStar_TypeChecker_Env.nbe)
                                 }) t
                               in
                            match uu____23737 with
                            | (uu____23746,ty,uu____23748) ->
                                eta_expand_with_type env t ty))
                | uu____23749 ->
                    let uu____23750 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___345_23758 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___345_23758.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___345_23758.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___345_23758.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___345_23758.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___345_23758.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___345_23758.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___345_23758.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___345_23758.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___345_23758.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___345_23758.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___345_23758.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___345_23758.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___345_23758.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___345_23758.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___345_23758.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___345_23758.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___345_23758.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___345_23758.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___345_23758.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___345_23758.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___345_23758.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___345_23758.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___345_23758.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___345_23758.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___345_23758.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___345_23758.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___345_23758.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___345_23758.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___345_23758.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___345_23758.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___345_23758.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___345_23758.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___345_23758.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___345_23758.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___345_23758.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___345_23758.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___345_23758.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___345_23758.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___345_23758.FStar_TypeChecker_Env.nbe)
                         }) t
                       in
                    (match uu____23750 with
                     | (uu____23759,ty,uu____23761) ->
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
      let uu___346_23842 = x  in
      let uu____23843 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___346_23842.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___346_23842.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____23843
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____23846 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____23869 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____23870 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____23871 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____23872 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____23879 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____23880 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____23881 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___347_23915 = rc  in
          let uu____23916 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____23925 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___347_23915.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____23916;
            FStar_Syntax_Syntax.residual_flags = uu____23925
          }  in
        let uu____23928 =
          let uu____23929 =
            let uu____23948 = elim_delayed_subst_binders bs  in
            let uu____23957 = elim_delayed_subst_term t2  in
            let uu____23960 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____23948, uu____23957, uu____23960)  in
          FStar_Syntax_Syntax.Tm_abs uu____23929  in
        mk1 uu____23928
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____23997 =
          let uu____23998 =
            let uu____24013 = elim_delayed_subst_binders bs  in
            let uu____24022 = elim_delayed_subst_comp c  in
            (uu____24013, uu____24022)  in
          FStar_Syntax_Syntax.Tm_arrow uu____23998  in
        mk1 uu____23997
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____24041 =
          let uu____24042 =
            let uu____24049 = elim_bv bv  in
            let uu____24050 = elim_delayed_subst_term phi  in
            (uu____24049, uu____24050)  in
          FStar_Syntax_Syntax.Tm_refine uu____24042  in
        mk1 uu____24041
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____24081 =
          let uu____24082 =
            let uu____24099 = elim_delayed_subst_term t2  in
            let uu____24102 = elim_delayed_subst_args args  in
            (uu____24099, uu____24102)  in
          FStar_Syntax_Syntax.Tm_app uu____24082  in
        mk1 uu____24081
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___348_24174 = p  in
              let uu____24175 =
                let uu____24176 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____24176  in
              {
                FStar_Syntax_Syntax.v = uu____24175;
                FStar_Syntax_Syntax.p =
                  (uu___348_24174.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___349_24178 = p  in
              let uu____24179 =
                let uu____24180 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____24180  in
              {
                FStar_Syntax_Syntax.v = uu____24179;
                FStar_Syntax_Syntax.p =
                  (uu___349_24178.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___350_24187 = p  in
              let uu____24188 =
                let uu____24189 =
                  let uu____24196 = elim_bv x  in
                  let uu____24197 = elim_delayed_subst_term t0  in
                  (uu____24196, uu____24197)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____24189  in
              {
                FStar_Syntax_Syntax.v = uu____24188;
                FStar_Syntax_Syntax.p =
                  (uu___350_24187.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___351_24220 = p  in
              let uu____24221 =
                let uu____24222 =
                  let uu____24235 =
                    FStar_List.map
                      (fun uu____24258  ->
                         match uu____24258 with
                         | (x,b) ->
                             let uu____24271 = elim_pat x  in
                             (uu____24271, b)) pats
                     in
                  (fv, uu____24235)  in
                FStar_Syntax_Syntax.Pat_cons uu____24222  in
              {
                FStar_Syntax_Syntax.v = uu____24221;
                FStar_Syntax_Syntax.p =
                  (uu___351_24220.FStar_Syntax_Syntax.p)
              }
          | uu____24284 -> p  in
        let elim_branch uu____24308 =
          match uu____24308 with
          | (pat,wopt,t3) ->
              let uu____24334 = elim_pat pat  in
              let uu____24337 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____24340 = elim_delayed_subst_term t3  in
              (uu____24334, uu____24337, uu____24340)
           in
        let uu____24345 =
          let uu____24346 =
            let uu____24369 = elim_delayed_subst_term t2  in
            let uu____24372 = FStar_List.map elim_branch branches  in
            (uu____24369, uu____24372)  in
          FStar_Syntax_Syntax.Tm_match uu____24346  in
        mk1 uu____24345
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____24503 =
          match uu____24503 with
          | (tc,topt) ->
              let uu____24538 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____24548 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____24548
                | FStar_Util.Inr c ->
                    let uu____24550 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____24550
                 in
              let uu____24551 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____24538, uu____24551)
           in
        let uu____24560 =
          let uu____24561 =
            let uu____24588 = elim_delayed_subst_term t2  in
            let uu____24591 = elim_ascription a  in
            (uu____24588, uu____24591, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____24561  in
        mk1 uu____24560
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___352_24652 = lb  in
          let uu____24653 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____24656 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___352_24652.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___352_24652.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____24653;
            FStar_Syntax_Syntax.lbeff =
              (uu___352_24652.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____24656;
            FStar_Syntax_Syntax.lbattrs =
              (uu___352_24652.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___352_24652.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____24659 =
          let uu____24660 =
            let uu____24673 =
              let uu____24680 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____24680)  in
            let uu____24689 = elim_delayed_subst_term t2  in
            (uu____24673, uu____24689)  in
          FStar_Syntax_Syntax.Tm_let uu____24660  in
        mk1 uu____24659
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____24733 =
          let uu____24734 =
            let uu____24741 = elim_delayed_subst_term tm  in
            (uu____24741, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____24734  in
        mk1 uu____24733
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____24752 =
          let uu____24753 =
            let uu____24760 = elim_delayed_subst_term t2  in
            let uu____24763 = elim_delayed_subst_meta md  in
            (uu____24760, uu____24763)  in
          FStar_Syntax_Syntax.Tm_meta uu____24753  in
        mk1 uu____24752

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___265_24772  ->
         match uu___265_24772 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____24776 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____24776
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
        let uu____24799 =
          let uu____24800 =
            let uu____24809 = elim_delayed_subst_term t  in
            (uu____24809, uopt)  in
          FStar_Syntax_Syntax.Total uu____24800  in
        mk1 uu____24799
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____24826 =
          let uu____24827 =
            let uu____24836 = elim_delayed_subst_term t  in
            (uu____24836, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____24827  in
        mk1 uu____24826
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___353_24845 = ct  in
          let uu____24846 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____24849 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____24860 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___353_24845.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___353_24845.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____24846;
            FStar_Syntax_Syntax.effect_args = uu____24849;
            FStar_Syntax_Syntax.flags = uu____24860
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___266_24863  ->
    match uu___266_24863 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____24877 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____24877
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____24916 =
          let uu____24923 = elim_delayed_subst_term t  in (m, uu____24923)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____24916
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____24935 =
          let uu____24944 = elim_delayed_subst_term t  in
          (m1, m2, uu____24944)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____24935
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
      (fun uu____24977  ->
         match uu____24977 with
         | (t,q) ->
             let uu____24996 = elim_delayed_subst_term t  in (uu____24996, q))
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
      (fun uu____25024  ->
         match uu____25024 with
         | (x,q) ->
             let uu____25043 =
               let uu___354_25044 = x  in
               let uu____25045 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___354_25044.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___354_25044.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____25045
               }  in
             (uu____25043, q)) bs

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
            | (uu____25151,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____25183,FStar_Util.Inl t) ->
                let uu____25205 =
                  let uu____25212 =
                    let uu____25213 =
                      let uu____25228 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____25228)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____25213  in
                  FStar_Syntax_Syntax.mk uu____25212  in
                uu____25205 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____25244 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____25244 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____25276 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____25349 ->
                    let uu____25350 =
                      let uu____25359 =
                        let uu____25360 = FStar_Syntax_Subst.compress t4  in
                        uu____25360.FStar_Syntax_Syntax.n  in
                      (uu____25359, tc)  in
                    (match uu____25350 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____25389) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____25436) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____25481,FStar_Util.Inl uu____25482) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____25513 -> failwith "Impossible")
                 in
              (match uu____25276 with
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
          let uu____25650 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____25650 with
          | (univ_names1,binders1,tc) ->
              let uu____25724 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____25724)
  
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
          let uu____25777 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____25777 with
          | (univ_names1,binders1,tc) ->
              let uu____25851 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____25851)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____25892 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____25892 with
           | (univ_names1,binders1,typ1) ->
               let uu___355_25932 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___355_25932.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___355_25932.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___355_25932.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___355_25932.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___356_25947 = s  in
          let uu____25948 =
            let uu____25949 =
              let uu____25958 = FStar_List.map (elim_uvars env) sigs  in
              (uu____25958, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____25949  in
          {
            FStar_Syntax_Syntax.sigel = uu____25948;
            FStar_Syntax_Syntax.sigrng =
              (uu___356_25947.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___356_25947.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___356_25947.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___356_25947.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____25975 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25975 with
           | (univ_names1,uu____25999,typ1) ->
               let uu___357_26021 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___357_26021.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___357_26021.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___357_26021.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___357_26021.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____26027 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____26027 with
           | (univ_names1,uu____26051,typ1) ->
               let uu___358_26073 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___358_26073.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___358_26073.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___358_26073.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___358_26073.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____26101 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____26101 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____26126 =
                            let uu____26127 =
                              let uu____26128 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____26128  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____26127
                             in
                          elim_delayed_subst_term uu____26126  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___359_26131 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___359_26131.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___359_26131.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___359_26131.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___359_26131.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___360_26132 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___360_26132.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___360_26132.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___360_26132.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___360_26132.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___361_26138 = s  in
          let uu____26139 =
            let uu____26140 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____26140  in
          {
            FStar_Syntax_Syntax.sigel = uu____26139;
            FStar_Syntax_Syntax.sigrng =
              (uu___361_26138.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___361_26138.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___361_26138.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___361_26138.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____26144 = elim_uvars_aux_t env us [] t  in
          (match uu____26144 with
           | (us1,uu____26168,t1) ->
               let uu___362_26190 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___362_26190.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___362_26190.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___362_26190.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___362_26190.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____26191 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____26193 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____26193 with
           | (univs1,binders,signature) ->
               let uu____26233 =
                 let uu____26238 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____26238 with
                 | (univs_opening,univs2) ->
                     let uu____26261 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____26261)
                  in
               (match uu____26233 with
                | (univs_opening,univs_closing) ->
                    let uu____26264 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____26270 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____26271 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____26270, uu____26271)  in
                    (match uu____26264 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____26297 =
                           match uu____26297 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____26315 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____26315 with
                                | (us1,t1) ->
                                    let uu____26326 =
                                      let uu____26335 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____26346 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____26335, uu____26346)  in
                                    (match uu____26326 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____26375 =
                                           let uu____26384 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____26395 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____26384, uu____26395)  in
                                         (match uu____26375 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____26425 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____26425
                                                 in
                                              let uu____26426 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____26426 with
                                               | (uu____26453,uu____26454,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____26477 =
                                                       let uu____26478 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____26478
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____26477
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____26487 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____26487 with
                           | (uu____26506,uu____26507,t1) -> t1  in
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
                             | uu____26583 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____26610 =
                               let uu____26611 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____26611.FStar_Syntax_Syntax.n  in
                             match uu____26610 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____26670 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____26703 =
                               let uu____26704 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____26704.FStar_Syntax_Syntax.n  in
                             match uu____26703 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____26727) ->
                                 let uu____26752 = destruct_action_body body
                                    in
                                 (match uu____26752 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____26801 ->
                                 let uu____26802 = destruct_action_body t  in
                                 (match uu____26802 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____26857 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____26857 with
                           | (action_univs,t) ->
                               let uu____26866 = destruct_action_typ_templ t
                                  in
                               (match uu____26866 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___363_26913 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___363_26913.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___363_26913.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___364_26915 = ed  in
                           let uu____26916 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____26917 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____26918 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____26919 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____26920 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____26921 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____26922 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____26923 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____26924 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____26925 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____26926 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____26927 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____26928 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____26929 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___364_26915.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___364_26915.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____26916;
                             FStar_Syntax_Syntax.bind_wp = uu____26917;
                             FStar_Syntax_Syntax.if_then_else = uu____26918;
                             FStar_Syntax_Syntax.ite_wp = uu____26919;
                             FStar_Syntax_Syntax.stronger = uu____26920;
                             FStar_Syntax_Syntax.close_wp = uu____26921;
                             FStar_Syntax_Syntax.assert_p = uu____26922;
                             FStar_Syntax_Syntax.assume_p = uu____26923;
                             FStar_Syntax_Syntax.null_wp = uu____26924;
                             FStar_Syntax_Syntax.trivial = uu____26925;
                             FStar_Syntax_Syntax.repr = uu____26926;
                             FStar_Syntax_Syntax.return_repr = uu____26927;
                             FStar_Syntax_Syntax.bind_repr = uu____26928;
                             FStar_Syntax_Syntax.actions = uu____26929;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___364_26915.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___365_26932 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___365_26932.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___365_26932.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___365_26932.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___365_26932.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___267_26953 =
            match uu___267_26953 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____26984 = elim_uvars_aux_t env us [] t  in
                (match uu____26984 with
                 | (us1,uu____27016,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___366_27047 = sub_eff  in
            let uu____27048 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____27051 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___366_27047.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___366_27047.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____27048;
              FStar_Syntax_Syntax.lift = uu____27051
            }  in
          let uu___367_27054 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___367_27054.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___367_27054.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___367_27054.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___367_27054.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____27064 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____27064 with
           | (univ_names1,binders1,comp1) ->
               let uu___368_27104 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___368_27104.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___368_27104.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___368_27104.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___368_27104.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____27107 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____27108 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      normalize
        [FStar_TypeChecker_Env.EraseUniverses;
        FStar_TypeChecker_Env.AllowUnboundUniverses] env t
  