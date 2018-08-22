open Prims
let cases :
  'Auu____11 'Auu____12 .
    ('Auu____11 -> 'Auu____12) ->
      'Auu____12 -> 'Auu____11 FStar_Pervasives_Native.option -> 'Auu____12
  =
  fun f  ->
    fun d  ->
      fun uu___251_32  ->
        match uu___251_32 with
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
  fun uu___252_1097  ->
    match uu___252_1097 with
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
  fun uu___253_1159  ->
    match uu___253_1159 with
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
  fun uu___254_1249  ->
    match uu___254_1249 with | [] -> true | uu____1252 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        (fun uu___273_1283  ->
           match () with
           | () ->
               let uu____1284 =
                 FStar_List.nth env x.FStar_Syntax_Syntax.index  in
               FStar_Pervasives_Native.snd uu____1284) ()
      with
      | uu___272_1301 ->
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
                 (fun uu___275_1463  ->
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
                                      (fun uu___255_1875  ->
                                         match uu___255_1875 with
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
                                                 (let uu___276_1899 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___276_1899.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___276_1899.FStar_Syntax_Syntax.sort)
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
                         let uu___277_1911 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___277_1911.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___277_1911.FStar_Syntax_Syntax.vars)
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
                           let uu___278_1950 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___278_1950.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___278_1950.FStar_Syntax_Syntax.index);
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
                             (let uu___279_2750 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___279_2750.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___279_2750.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____2734))
                       in
                    (match uu____2704 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___280_2768 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___280_2768.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___280_2768.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___280_2768.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___280_2768.FStar_Syntax_Syntax.lbpos)
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
                             (let uu___281_2906 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___281_2906.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___281_2906.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___282_2907 = lb  in
                      let uu____2908 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___282_2907.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___282_2907.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____2908;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___282_2907.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___282_2907.FStar_Syntax_Syntax.lbpos)
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
                      let uu___283_3157 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___283_3157.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___283_3157.FStar_Syntax_Syntax.vars)
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
                                ((let uu___284_3743 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___284_3743.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___285_3762 = x  in
                             let uu____3763 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___285_3762.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___285_3762.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3763
                             }  in
                           ((let uu___286_3777 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___286_3777.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___287_3788 = x  in
                             let uu____3789 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___287_3788.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___287_3788.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3789
                             }  in
                           ((let uu___288_3803 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___288_3803.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___289_3819 = x  in
                             let uu____3820 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___289_3819.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___289_3819.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3820
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___290_3837 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___290_3837.FStar_Syntax_Syntax.p)
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
                          let uu___291_4515 = b  in
                          let uu____4516 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___291_4515.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___291_4515.FStar_Syntax_Syntax.index);
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
                        (fun uu___256_4776  ->
                           match uu___256_4776 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4780 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____4780
                           | f -> f))
                    in
                 let uu____4784 =
                   let uu___292_4785 = c1  in
                   let uu____4786 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4786;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___292_4785.FStar_Syntax_Syntax.effect_name);
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
         (fun uu___257_4796  ->
            match uu___257_4796 with
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
                   (fun uu___258_4818  ->
                      match uu___258_4818 with
                      | FStar_Syntax_Syntax.DECREASES uu____4819 -> false
                      | uu____4822 -> true))
               in
            let rc1 =
              let uu___293_4824 = rc  in
              let uu____4825 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___293_4824.FStar_Syntax_Syntax.residual_effect);
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
                                      let uu___294_5146 = bv  in
                                      let uu____5147 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___294_5146.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___294_5146.FStar_Syntax_Syntax.index);
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
                                      (fun uu___259_5176  ->
                                         match uu___259_5176 with
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
          (let uu___295_5649 = cfg  in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___296_5652 = FStar_TypeChecker_Cfg.default_steps  in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___296_5652.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___296_5652.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___296_5652.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___296_5652.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___296_5652.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___296_5652.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___296_5652.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___296_5652.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___296_5652.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___296_5652.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___296_5652.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___296_5652.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___296_5652.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___296_5652.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___296_5652.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___296_5652.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___296_5652.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___296_5652.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___296_5652.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___296_5652.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___296_5652.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___296_5652.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___296_5652.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___296_5652.FStar_TypeChecker_Cfg.nbe_step)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___295_5649.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___295_5649.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___295_5649.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___295_5649.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___295_5649.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___295_5649.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___295_5649.FStar_TypeChecker_Cfg.reifying)
           }) tm
  
let is_norm_request :
  'Auu____5659 .
    FStar_Syntax_Syntax.term -> 'Auu____5659 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____5674 =
        let uu____5681 =
          let uu____5682 = FStar_Syntax_Util.un_uinst hd1  in
          uu____5682.FStar_Syntax_Syntax.n  in
        (uu____5681, args)  in
      match uu____5674 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5688::uu____5689::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5693::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____5698::uu____5699::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____5702 -> false
  
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s  ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
  
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___260_5724  ->
    match uu___260_5724 with
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
        let uu____5730 =
          let uu____5733 =
            let uu____5734 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldOnly uu____5734  in
          [uu____5733]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____5730
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____5740 =
          let uu____5743 =
            let uu____5744 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldFully uu____5744  in
          [uu____5743]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____5740
    | FStar_Syntax_Embeddings.UnfoldAttr names1 ->
        let uu____5750 =
          let uu____5753 =
            let uu____5754 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldAttr uu____5754  in
          [uu____5753]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____5750
    | FStar_Syntax_Embeddings.NBE  -> [FStar_TypeChecker_Env.NBE]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  = fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____5776 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term,'Auu____5776)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____5827 =
            let uu____5832 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____5832 s  in
          match uu____5827 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____5848 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____5848
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
        | uu____5877::(tm,uu____5879)::[] ->
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
        | (tm,uu____5908)::[] ->
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
        | (steps,uu____5929)::uu____5930::(tm,uu____5932)::[] ->
            let add_exclude s z =
              let uu____5970 =
                FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s  in
              if uu____5970
              then s
              else (FStar_TypeChecker_Env.Exclude z) :: s  in
            let uu____5974 =
              let uu____5979 = full_norm steps  in parse_steps uu____5979  in
            (match uu____5974 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = FStar_TypeChecker_Env.Beta :: s  in
                 let s2 = add_exclude s1 FStar_TypeChecker_Env.Zeta  in
                 let s3 = add_exclude s2 FStar_TypeChecker_Env.Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____6018 -> FStar_Pervasives_Native.None
  
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun s  ->
      fun tm  ->
        let delta_level =
          let uu____6049 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___261_6054  ->
                    match uu___261_6054 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____6055 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____6056 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____6059 -> true
                    | uu____6062 -> false))
             in
          if uu____6049
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta]  in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____6069  ->
             let uu____6070 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____6070);
        (let tm_norm =
           let uu____6072 =
             let uu____6087 = FStar_TypeChecker_Cfg.cfg_env cfg  in
             uu____6087.FStar_TypeChecker_Env.nbe  in
           uu____6072 s cfg.FStar_TypeChecker_Cfg.tcenv tm  in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____6091  ->
              let uu____6092 = FStar_Syntax_Print.term_to_string tm_norm  in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____6092);
         tm_norm)
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___262_6099  ->
    match uu___262_6099 with
    | (App
        (uu____6102,{
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reify );
                      FStar_Syntax_Syntax.pos = uu____6103;
                      FStar_Syntax_Syntax.vars = uu____6104;_},uu____6105,uu____6106))::uu____6107
        -> true
    | uu____6112 -> false
  
let firstn :
  'Auu____6121 .
    Prims.int ->
      'Auu____6121 Prims.list ->
        ('Auu____6121 Prims.list,'Auu____6121 Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack  ->
      let rec drop_irrel uu___263_6172 =
        match uu___263_6172 with
        | (MemoLazy uu____6177)::s -> drop_irrel s
        | s -> s  in
      let uu____6190 = drop_irrel stack  in
      match uu____6190 with
      | (App
          (uu____6193,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____6194;
                        FStar_Syntax_Syntax.vars = uu____6195;_},uu____6196,uu____6197))::uu____6198
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____6203 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____6226) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____6236) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____6257  ->
                  match uu____6257 with
                  | (a,uu____6267) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6277 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____6300 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____6301 -> false
    | FStar_Syntax_Syntax.Tm_type uu____6314 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____6315 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____6316 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____6317 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____6318 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____6319 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____6326 -> false
    | FStar_Syntax_Syntax.Tm_let uu____6333 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____6346 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____6365 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____6380 -> true
    | FStar_Syntax_Syntax.Tm_match uu____6387 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____6457  ->
                   match uu____6457 with
                   | (a,uu____6467) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____6478) ->
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
                     (fun uu____6606  ->
                        match uu____6606 with
                        | (a,uu____6616) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____6625,uu____6626,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____6632,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____6638 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____6645 -> false
            | FStar_Syntax_Syntax.Meta_named uu____6646 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____6652 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____6658 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_fully  -> true | uu____6664 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_reify  -> true | uu____6670 -> false
  
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
            let uu____6699 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
            match uu____6699 with
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
              (fun uu____6827  ->
                 fun uu____6828  ->
                   match (uu____6827, uu____6828) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____6888 =
            match uu____6888 with
            | (x,y,z) ->
                let uu____6898 = FStar_Util.string_of_bool x  in
                let uu____6899 = FStar_Util.string_of_bool y  in
                let uu____6900 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____6898 uu____6899
                  uu____6900
             in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg  in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____6919  ->
                    let uu____6920 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____6921 = FStar_Util.string_of_bool b  in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____6920 uu____6921);
               if b then reif else no)
            else
              if
                (let uu____6929 = FStar_TypeChecker_Cfg.find_prim_step cfg fv
                    in
                 FStar_Option.isSome uu____6929)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____6934  ->
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
                          ((is_rec,uu____6968),uu____6969);
                        FStar_Syntax_Syntax.sigrng = uu____6970;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____6972;
                        FStar_Syntax_Syntax.sigattrs = uu____6973;_},uu____6974),uu____6975),uu____6976,uu____6977,uu____6978)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7083  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____7084,uu____7085,uu____7086,uu____7087) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7154  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____7156),uu____7157);
                        FStar_Syntax_Syntax.sigrng = uu____7158;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7160;
                        FStar_Syntax_Syntax.sigattrs = uu____7161;_},uu____7162),uu____7163),uu____7164,uu____7165,uu____7166)
                     when
                     is_rec &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7271  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____7272,FStar_Pervasives_Native.Some
                    uu____7273,uu____7274,uu____7275) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7343  ->
                           let uu____7344 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____7344);
                      (let uu____7345 =
                         let uu____7354 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____7374 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____7374
                            in
                         let uu____7381 =
                           let uu____7390 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____7410 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____7410
                              in
                           let uu____7421 =
                             let uu____7430 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____7450 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____7450
                                in
                             [uu____7430]  in
                           uu____7390 :: uu____7421  in
                         uu____7354 :: uu____7381  in
                       comb_or uu____7345))
                 | (uu____7481,uu____7482,FStar_Pervasives_Native.Some
                    uu____7483,uu____7484) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7552  ->
                           let uu____7553 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____7553);
                      (let uu____7554 =
                         let uu____7563 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____7583 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____7583
                            in
                         let uu____7590 =
                           let uu____7599 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____7619 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____7619
                              in
                           let uu____7630 =
                             let uu____7639 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____7659 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____7659
                                in
                             [uu____7639]  in
                           uu____7599 :: uu____7630  in
                         uu____7563 :: uu____7590  in
                       comb_or uu____7554))
                 | (uu____7690,uu____7691,uu____7692,FStar_Pervasives_Native.Some
                    uu____7693) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7761  ->
                           let uu____7762 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____7762);
                      (let uu____7763 =
                         let uu____7772 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____7792 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____7792
                            in
                         let uu____7799 =
                           let uu____7808 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____7828 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____7828
                              in
                           let uu____7839 =
                             let uu____7848 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____7868 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____7868
                                in
                             [uu____7848]  in
                           uu____7808 :: uu____7839  in
                         uu____7772 :: uu____7799  in
                       comb_or uu____7763))
                 | uu____7899 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7945  ->
                           let uu____7946 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____7947 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____7948 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level
                              in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____7946 uu____7947 uu____7948);
                      (let uu____7949 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___264_7953  ->
                                 match uu___264_7953 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.InliningDelta  ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____7955 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv
                                        in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____7955 l))
                          in
                       FStar_All.pipe_left yesno uu____7949)))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____7967  ->
               let uu____7968 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____7969 =
                 let uu____7970 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____7970  in
               let uu____7971 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____7968 uu____7969 uu____7971);
          (match res with
           | (false ,uu____7972,uu____7973) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____7974 ->
               let uu____7981 =
                 let uu____7982 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____7982
                  in
               FStar_All.pipe_left failwith uu____7981)
  
let decide_unfolding :
  'Auu____7997 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'Auu____7997 ->
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
                    let uu___297_8066 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___298_8069 = cfg.FStar_TypeChecker_Cfg.steps
                            in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___298_8069.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___298_8069.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___298_8069.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___298_8069.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___298_8069.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___298_8069.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___298_8069.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___298_8069.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___298_8069.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___298_8069.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___298_8069.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___298_8069.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___298_8069.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___298_8069.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___298_8069.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___298_8069.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___298_8069.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___298_8069.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___298_8069.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___298_8069.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___298_8069.FStar_TypeChecker_Cfg.nbe_step)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___297_8066.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___297_8066.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___297_8066.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___297_8066.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___297_8066.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___297_8066.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___297_8066.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___297_8066.FStar_TypeChecker_Cfg.reifying)
                    }  in
                  let stack' =
                    match stack with
                    | (UnivArgs (us,r))::stack' -> (UnivArgs (us, r)) ::
                        (Cfg cfg) :: stack'
                    | stack' -> (Cfg cfg) :: stack'  in
                  FStar_Pervasives_Native.Some (cfg', stack')
              | Should_unfold_reify  ->
                  let ref =
                    let uu____8106 =
                      let uu____8113 =
                        let uu____8114 =
                          let uu____8115 = FStar_Syntax_Syntax.lid_of_fv fv
                             in
                          FStar_Const.Const_reflect uu____8115  in
                        FStar_Syntax_Syntax.Tm_constant uu____8114  in
                      FStar_Syntax_Syntax.mk uu____8113  in
                    uu____8106 FStar_Pervasives_Native.None
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
               | FStar_Syntax_Syntax.Tm_delayed uu____8403 ->
                   let uu____8426 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____8426
               | uu____8427 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____8436  ->
               let uu____8437 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____8438 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____8439 = FStar_Syntax_Print.term_to_string t1  in
               let uu____8440 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____8447 =
                 let uu____8448 =
                   let uu____8451 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8451
                    in
                 stack_to_string uu____8448  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____8437 uu____8438 uu____8439 uu____8440 uu____8447);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____8477  ->
               let uu____8478 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____8478);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8482  ->
                     let uu____8483 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8483);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____8484 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8488  ->
                     let uu____8489 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8489);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____8490 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8494  ->
                     let uu____8495 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8495);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____8496 ->
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
               let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid
                  in
               let uu____8526 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
               (match uu____8526 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level _0_17) when
                    _0_17 = (Prims.parse_int "0") ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____8532  ->
                          let uu____8533 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____8533);
                     rebuild cfg env stack t1)
                | uu____8534 ->
                    let uu____8537 =
                      decide_unfolding cfg env stack
                        t1.FStar_Syntax_Syntax.pos fv qninfo
                       in
                    (match uu____8537 with
                     | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                         do_unfold_fv cfg1 env stack1 t1 qninfo fv
                     | FStar_Pervasives_Native.None  ->
                         rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_quoted uu____8564 ->
               let uu____8571 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____8571
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
                  && (is_norm_request hd1 args))
                 &&
                 (let uu____8607 =
                    FStar_Ident.lid_equals
                      (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____8607)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___299_8611 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___300_8614 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___300_8614.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___300_8614.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___300_8614.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___300_8614.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___300_8614.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___300_8614.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___300_8614.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___300_8614.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___300_8614.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___300_8614.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___300_8614.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___300_8614.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___300_8614.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___300_8614.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___300_8614.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___300_8614.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___300_8614.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___300_8614.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___300_8614.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___300_8614.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___300_8614.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___300_8614.FStar_TypeChecker_Cfg.nbe_step)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___299_8611.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___299_8611.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___299_8611.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___299_8611.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___299_8611.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___299_8611.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____8619 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____8619 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____8652  ->
                                 fun stack1  ->
                                   match uu____8652 with
                                   | (a,aq) ->
                                       let uu____8664 =
                                         let uu____8665 =
                                           let uu____8672 =
                                             let uu____8673 =
                                               let uu____8704 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____8704, false)
                                                in
                                             Clos uu____8673  in
                                           (uu____8672, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____8665  in
                                       uu____8664 :: stack1) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____8792  ->
                            let uu____8793 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____8793);
                       norm cfg env stack1 hd1))
                 | FStar_Pervasives_Native.Some (s,tm) when is_nbe_request s
                     ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____8815 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting NBE request on %s ... \n" uu____8815)
                      else ();
                      (let tm' = closure_as_term cfg env tm  in
                       let start = FStar_Util.now ()  in
                       let tm_norm = nbe_eval cfg s tm'  in
                       let fin = FStar_Util.now ()  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         (let uu____8822 =
                            let uu____8823 =
                              let uu____8824 = FStar_Util.time_diff start fin
                                 in
                              FStar_Pervasives_Native.snd uu____8824  in
                            FStar_Util.string_of_int uu____8823  in
                          let uu____8829 =
                            FStar_Syntax_Print.term_to_string tm'  in
                          let uu____8830 =
                            FStar_Syntax_Print.term_to_string tm_norm  in
                          FStar_Util.print3 "NBE'd (%s ms) %s\n\tto %s\n"
                            uu____8822 uu____8829 uu____8830)
                       else ();
                       norm cfg env stack tm_norm))
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____8845 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting norm request on %s ... \n" uu____8845)
                      else ();
                      (let delta_level =
                         let uu____8850 =
                           FStar_All.pipe_right s
                             (FStar_Util.for_some
                                (fun uu___265_8855  ->
                                   match uu___265_8855 with
                                   | FStar_TypeChecker_Env.UnfoldUntil
                                       uu____8856 -> true
                                   | FStar_TypeChecker_Env.UnfoldOnly
                                       uu____8857 -> true
                                   | FStar_TypeChecker_Env.UnfoldFully
                                       uu____8860 -> true
                                   | uu____8863 -> false))
                            in
                         if uu____8850
                         then
                           [FStar_TypeChecker_Env.Unfold
                              FStar_Syntax_Syntax.delta_constant]
                         else [FStar_TypeChecker_Env.NoDelta]  in
                       let cfg'1 =
                         let uu___301_8868 = cfg  in
                         let uu____8869 =
                           let uu___302_8870 =
                             FStar_TypeChecker_Cfg.to_fsteps s  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___302_8870.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___302_8870.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___302_8870.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak =
                               (uu___302_8870.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___302_8870.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___302_8870.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___302_8870.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___302_8870.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               (uu___302_8870.FStar_TypeChecker_Cfg.unfold_only);
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___302_8870.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___302_8870.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___302_8870.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___302_8870.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___302_8870.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___302_8870.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___302_8870.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___302_8870.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___302_8870.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___302_8870.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___302_8870.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___302_8870.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___302_8870.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               true;
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___302_8870.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___302_8870.FStar_TypeChecker_Cfg.nbe_step)
                           }  in
                         {
                           FStar_TypeChecker_Cfg.steps = uu____8869;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___301_8868.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___301_8868.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = delta_level;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___301_8868.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong =
                             (uu___301_8868.FStar_TypeChecker_Cfg.strong);
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___301_8868.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___301_8868.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let stack' =
                         let tail1 = (Cfg cfg) :: stack  in
                         if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           let uu____8875 =
                             let uu____8876 =
                               let uu____8881 = FStar_Util.now ()  in
                               (t1, uu____8881)  in
                             Debug uu____8876  in
                           uu____8875 :: tail1
                         else tail1  in
                       norm cfg'1 env stack' tm))))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____8885 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____8885
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____8894 =
                      let uu____8901 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____8901, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____8894  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____8910 = lookup_bvar env x  in
               (match uu____8910 with
                | Univ uu____8911 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                    then
                      let uu____8960 = FStar_ST.op_Bang r  in
                      (match uu____8960 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9078  ->
                                 let uu____9079 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____9080 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____9079
                                   uu____9080);
                            (let uu____9081 = maybe_weakly_reduced t'  in
                             if uu____9081
                             then
                               match stack with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____9082 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____9157)::uu____9158 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____9168,uu____9169))::stack_rest ->
                    (match c with
                     | Univ uu____9173 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____9182 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____9211  ->
                                    let uu____9212 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____9212);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____9246  ->
                                    let uu____9247 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____9247);
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
                       (fun uu____9315  ->
                          let uu____9316 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____9316);
                     norm cfg env stack1 t1)
                | (Match uu____9317)::uu____9318 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9331 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9331 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9367  -> dummy :: env1) env)
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
                                          let uu____9410 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9410)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___303_9417 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___303_9417.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___303_9417.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9418 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9424  ->
                                 let uu____9425 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9425);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___304_9436 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___304_9436.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___304_9436.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___304_9436.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___304_9436.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___304_9436.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___304_9436.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___304_9436.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___304_9436.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____9439)::uu____9440 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9449 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9449 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9485  -> dummy :: env1) env)
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
                                          let uu____9528 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9528)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___303_9535 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___303_9535.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___303_9535.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9536 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9542  ->
                                 let uu____9543 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9543);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___304_9554 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___304_9554.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___304_9554.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___304_9554.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___304_9554.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___304_9554.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___304_9554.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___304_9554.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___304_9554.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____9557)::uu____9558 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9569 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9569 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9605  -> dummy :: env1) env)
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
                                          let uu____9648 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9648)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___303_9655 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___303_9655.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___303_9655.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9656 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9662  ->
                                 let uu____9663 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9663);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___304_9674 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___304_9674.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___304_9674.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___304_9674.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___304_9674.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___304_9674.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___304_9674.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___304_9674.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___304_9674.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____9677)::uu____9678 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9691 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9691 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9727  -> dummy :: env1) env)
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
                                          let uu____9770 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9770)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___303_9777 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___303_9777.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___303_9777.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9778 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9784  ->
                                 let uu____9785 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9785);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___304_9796 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___304_9796.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___304_9796.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___304_9796.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___304_9796.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___304_9796.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___304_9796.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___304_9796.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___304_9796.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____9799)::uu____9800 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9813 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9813 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9849  -> dummy :: env1) env)
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
                                          let uu____9892 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9892)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___303_9899 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___303_9899.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___303_9899.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9900 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9906  ->
                                 let uu____9907 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9907);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___304_9918 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___304_9918.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___304_9918.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___304_9918.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___304_9918.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___304_9918.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___304_9918.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___304_9918.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___304_9918.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____9921)::uu____9922 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9939 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9939 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9975  -> dummy :: env1) env)
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
                                          let uu____10018 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10018)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___303_10025 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___303_10025.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___303_10025.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10026 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10032  ->
                                 let uu____10033 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10033);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___304_10044 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___304_10044.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___304_10044.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___304_10044.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___304_10044.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___304_10044.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___304_10044.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___304_10044.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___304_10044.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____10049 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10049 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10085  -> dummy :: env1) env)
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
                                          let uu____10128 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10128)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___303_10135 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___303_10135.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___303_10135.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10136 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10142  ->
                                 let uu____10143 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10143);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___304_10154 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___304_10154.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___304_10154.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___304_10154.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___304_10154.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___304_10154.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___304_10154.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___304_10154.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___304_10154.FStar_TypeChecker_Cfg.reifying)
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
                      (fun uu____10197  ->
                         fun stack1  ->
                           match uu____10197 with
                           | (a,aq) ->
                               let uu____10209 =
                                 let uu____10210 =
                                   let uu____10217 =
                                     let uu____10218 =
                                       let uu____10249 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____10249, false)  in
                                     Clos uu____10218  in
                                   (uu____10217, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____10210  in
                               uu____10209 :: stack1) args)
                  in
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____10337  ->
                     let uu____10338 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____10338);
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
                             ((let uu___305_10386 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___305_10386.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___305_10386.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____10387 ->
                      let uu____10402 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10402)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____10405 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____10405 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____10436 =
                          let uu____10437 =
                            let uu____10444 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___306_10450 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___306_10450.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___306_10450.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____10444)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____10437  in
                        mk uu____10436 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____10473 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____10473
               else
                 (let uu____10475 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____10475 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____10483 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____10509  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____10483 c1  in
                      let t2 =
                        let uu____10533 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____10533 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____10646)::uu____10647 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10660  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____10661)::uu____10662 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10673  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____10674,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____10675;
                                   FStar_Syntax_Syntax.vars = uu____10676;_},uu____10677,uu____10678))::uu____10679
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10686  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____10687)::uu____10688 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10699  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____10700 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10703  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____10707  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____10732 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____10732
                         | FStar_Util.Inr c ->
                             let uu____10746 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____10746
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____10769 =
                               let uu____10770 =
                                 let uu____10797 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____10797, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____10770
                                in
                             mk uu____10769 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____10832 ->
                           let uu____10833 =
                             let uu____10834 =
                               let uu____10835 =
                                 let uu____10862 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____10862, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____10835
                                in
                             mk uu____10834 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____10833))))
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
                   let uu___307_10939 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___308_10942 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___308_10942.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___308_10942.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___308_10942.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___308_10942.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___308_10942.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___308_10942.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___308_10942.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___308_10942.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___308_10942.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___308_10942.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___308_10942.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___308_10942.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___308_10942.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___308_10942.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___308_10942.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___308_10942.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___308_10942.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___308_10942.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___308_10942.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___308_10942.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___308_10942.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___308_10942.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___308_10942.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___308_10942.FStar_TypeChecker_Cfg.nbe_step)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___307_10939.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___307_10939.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___307_10939.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___307_10939.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___307_10939.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___307_10939.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___307_10939.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___307_10939.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____10978 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____10978 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___309_10998 = cfg  in
                               let uu____10999 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___309_10998.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____10999;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___309_10998.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___309_10998.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___309_10998.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___309_10998.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___309_10998.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___309_10998.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___309_10998.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____11006 =
                                 let uu____11007 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____11007  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____11006
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___310_11010 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___310_11010.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___310_11010.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___310_11010.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___310_11010.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____11011 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____11011
           | FStar_Syntax_Syntax.Tm_let
               ((uu____11022,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____11023;
                               FStar_Syntax_Syntax.lbunivs = uu____11024;
                               FStar_Syntax_Syntax.lbtyp = uu____11025;
                               FStar_Syntax_Syntax.lbeff = uu____11026;
                               FStar_Syntax_Syntax.lbdef = uu____11027;
                               FStar_Syntax_Syntax.lbattrs = uu____11028;
                               FStar_Syntax_Syntax.lbpos = uu____11029;_}::uu____11030),uu____11031)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name
                   cfg.FStar_TypeChecker_Cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____11071 =
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
               if uu____11071
               then
                 let binder =
                   let uu____11073 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____11073  in
                 let env1 =
                   let uu____11083 =
                     let uu____11090 =
                       let uu____11091 =
                         let uu____11122 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____11122,
                           false)
                          in
                       Clos uu____11091  in
                     ((FStar_Pervasives_Native.Some binder), uu____11090)  in
                   uu____11083 :: env  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____11217  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                 then
                   (FStar_TypeChecker_Cfg.log cfg
                      (fun uu____11221  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____11222 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____11222))
                 else
                   (let uu____11224 =
                      let uu____11229 =
                        let uu____11230 =
                          let uu____11237 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____11237
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____11230]  in
                      FStar_Syntax_Subst.open_term uu____11229 body  in
                    match uu____11224 with
                    | (bs,body1) ->
                        (FStar_TypeChecker_Cfg.log cfg
                           (fun uu____11264  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____11272 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____11272  in
                            FStar_Util.Inl
                              (let uu___311_11288 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___311_11288.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___311_11288.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____11291  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___312_11293 = lb  in
                             let uu____11294 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___312_11293.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___312_11293.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____11294;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___312_11293.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___312_11293.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11323  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___313_11348 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps =
                                 (uu___313_11348.FStar_TypeChecker_Cfg.steps);
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___313_11348.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___313_11348.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 (uu___313_11348.FStar_TypeChecker_Cfg.delta_level);
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___313_11348.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong = true;
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___313_11348.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___313_11348.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___313_11348.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           FStar_TypeChecker_Cfg.log cfg1
                             (fun uu____11351  ->
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
               let uu____11368 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____11368 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____11404 =
                               let uu___314_11405 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___314_11405.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___314_11405.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____11404  in
                           let uu____11406 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____11406 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____11432 =
                                   FStar_List.map (fun uu____11448  -> dummy)
                                     lbs1
                                    in
                                 let uu____11449 =
                                   let uu____11458 =
                                     FStar_List.map
                                       (fun uu____11480  -> dummy) xs1
                                      in
                                   FStar_List.append uu____11458 env  in
                                 FStar_List.append uu____11432 uu____11449
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____11506 =
                                       let uu___315_11507 = rc  in
                                       let uu____11508 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___315_11507.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____11508;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___315_11507.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____11506
                                 | uu____11517 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___316_11523 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___316_11523.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___316_11523.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___316_11523.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___316_11523.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____11533 =
                        FStar_List.map (fun uu____11549  -> dummy) lbs2  in
                      FStar_List.append uu____11533 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____11557 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____11557 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___317_11573 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___317_11573.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___317_11573.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
               ->
               let uu____11602 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____11602
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____11621 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____11697  ->
                        match uu____11697 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___318_11818 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___318_11818.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___318_11818.FStar_Syntax_Syntax.sort)
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
               (match uu____11621 with
                | (rec_env,memos,uu____12045) ->
                    let uu____12098 =
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
                             let uu____12409 =
                               let uu____12416 =
                                 let uu____12417 =
                                   let uu____12448 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____12448, false)
                                    in
                                 Clos uu____12417  in
                               (FStar_Pervasives_Native.None, uu____12416)
                                in
                             uu____12409 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____12552  ->
                     let uu____12553 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____12553);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____12575 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____12577::uu____12578 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____12583) ->
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
                             | uu____12610 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____12626 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____12626
                              | uu____12639 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____12645 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____12669 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____12683 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____12696 =
                        let uu____12697 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____12698 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____12697 uu____12698
                         in
                      failwith uu____12696
                    else
                      (let uu____12700 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____12700)
                | uu____12701 -> norm cfg env stack t2))

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
              let uu____12710 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____12710 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____12724  ->
                        let uu____12725 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____12725);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____12736  ->
                        let uu____12737 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____12738 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____12737 uu____12738);
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
                      | (UnivArgs (us',uu____12751))::stack1 ->
                          ((let uu____12760 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____12760
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____12764 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____12764) us'
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
                      | uu____12797 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____12800 ->
                          let uu____12803 =
                            let uu____12804 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____12804
                             in
                          failwith uu____12803
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
                  let uu___319_12828 = cfg  in
                  let uu____12829 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____12829;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___319_12828.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___319_12828.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___319_12828.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___319_12828.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___319_12828.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___319_12828.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___319_12828.FStar_TypeChecker_Cfg.reifying)
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
                     (uu____12859,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____12860;
                                    FStar_Syntax_Syntax.vars = uu____12861;_},uu____12862,uu____12863))::uu____12864
                     -> ()
                 | uu____12869 ->
                     let uu____12872 =
                       let uu____12873 = stack_to_string stack  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____12873
                        in
                     failwith uu____12872);
                (let head0 = head1  in
                 let head2 = FStar_Syntax_Util.unascribe head1  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____12880  ->
                      let uu____12881 = FStar_Syntax_Print.tag_of_term head2
                         in
                      let uu____12882 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____12881
                        uu____12882);
                 (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                  let uu____12884 =
                    let uu____12885 = FStar_Syntax_Subst.compress head3  in
                    uu____12885.FStar_Syntax_Syntax.n  in
                  match uu____12884 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let ed =
                        let uu____12903 =
                          FStar_TypeChecker_Env.norm_eff_name
                            cfg.FStar_TypeChecker_Cfg.tcenv m
                           in
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv uu____12903
                         in
                      let uu____12904 = ed.FStar_Syntax_Syntax.bind_repr  in
                      (match uu____12904 with
                       | (uu____12905,bind_repr) ->
                           (match lb.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____12915 ->
                                failwith
                                  "Cannot reify a top-level let binding"
                            | FStar_Util.Inl x ->
                                let is_return e =
                                  let uu____12925 =
                                    let uu____12926 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____12926.FStar_Syntax_Syntax.n  in
                                  match uu____12925 with
                                  | FStar_Syntax_Syntax.Tm_meta
                                      (e1,FStar_Syntax_Syntax.Meta_monadic
                                       (uu____12932,uu____12933))
                                      ->
                                      let uu____12942 =
                                        let uu____12943 =
                                          FStar_Syntax_Subst.compress e1  in
                                        uu____12943.FStar_Syntax_Syntax.n  in
                                      (match uu____12942 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                            (uu____12949,msrc,uu____12951))
                                           when
                                           FStar_Syntax_Util.is_pure_effect
                                             msrc
                                           ->
                                           let uu____12960 =
                                             FStar_Syntax_Subst.compress e2
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____12960
                                       | uu____12961 ->
                                           FStar_Pervasives_Native.None)
                                  | uu____12962 ->
                                      FStar_Pervasives_Native.None
                                   in
                                let uu____12963 =
                                  is_return lb.FStar_Syntax_Syntax.lbdef  in
                                (match uu____12963 with
                                 | FStar_Pervasives_Native.Some e ->
                                     let lb1 =
                                       let uu___320_12968 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___320_12968.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___320_12968.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           (uu___320_12968.FStar_Syntax_Syntax.lbtyp);
                                         FStar_Syntax_Syntax.lbeff =
                                           FStar_Parser_Const.effect_PURE_lid;
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___320_12968.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___320_12968.FStar_Syntax_Syntax.lbpos)
                                       }  in
                                     let uu____12969 = FStar_List.tl stack
                                        in
                                     let uu____12970 =
                                       let uu____12971 =
                                         let uu____12978 =
                                           let uu____12979 =
                                             let uu____12992 =
                                               FStar_Syntax_Util.mk_reify
                                                 body
                                                in
                                             ((false, [lb1]), uu____12992)
                                              in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____12979
                                            in
                                         FStar_Syntax_Syntax.mk uu____12978
                                          in
                                       uu____12971
                                         FStar_Pervasives_Native.None
                                         head3.FStar_Syntax_Syntax.pos
                                        in
                                     norm cfg env uu____12969 uu____12970
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____13008 =
                                       let uu____13009 = is_return body  in
                                       match uu____13009 with
                                       | FStar_Pervasives_Native.Some
                                           {
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_bvar y;
                                             FStar_Syntax_Syntax.pos =
                                               uu____13013;
                                             FStar_Syntax_Syntax.vars =
                                               uu____13014;_}
                                           -> FStar_Syntax_Syntax.bv_eq x y
                                       | uu____13017 -> false  in
                                     if uu____13008
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
                                          let uu____13038 =
                                            let uu____13045 =
                                              let uu____13046 =
                                                let uu____13065 =
                                                  let uu____13074 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____13074]  in
                                                (uu____13065, body1,
                                                  (FStar_Pervasives_Native.Some
                                                     body_rc))
                                                 in
                                              FStar_Syntax_Syntax.Tm_abs
                                                uu____13046
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____13045
                                             in
                                          uu____13038
                                            FStar_Pervasives_Native.None
                                            body1.FStar_Syntax_Syntax.pos
                                           in
                                        let close1 = closure_as_term cfg env
                                           in
                                        let bind_inst =
                                          let uu____13116 =
                                            let uu____13117 =
                                              FStar_Syntax_Subst.compress
                                                bind_repr
                                               in
                                            uu____13117.FStar_Syntax_Syntax.n
                                             in
                                          match uu____13116 with
                                          | FStar_Syntax_Syntax.Tm_uinst
                                              (bind1,uu____13123::uu____13124::[])
                                              ->
                                              let uu____13129 =
                                                let uu____13136 =
                                                  let uu____13137 =
                                                    let uu____13144 =
                                                      let uu____13145 =
                                                        let uu____13146 =
                                                          close1
                                                            lb.FStar_Syntax_Syntax.lbtyp
                                                           in
                                                        (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.FStar_TypeChecker_Cfg.tcenv
                                                          uu____13146
                                                         in
                                                      let uu____13147 =
                                                        let uu____13150 =
                                                          let uu____13151 =
                                                            close1 t  in
                                                          (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                            cfg.FStar_TypeChecker_Cfg.tcenv
                                                            uu____13151
                                                           in
                                                        [uu____13150]  in
                                                      uu____13145 ::
                                                        uu____13147
                                                       in
                                                    (bind1, uu____13144)  in
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                    uu____13137
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____13136
                                                 in
                                              uu____13129
                                                FStar_Pervasives_Native.None
                                                rng
                                          | uu____13157 ->
                                              failwith
                                                "NIY : Reification of indexed effects"
                                           in
                                        let maybe_range_arg =
                                          let uu____13171 =
                                            FStar_Util.for_some
                                              (FStar_Syntax_Util.attr_eq
                                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                                              ed.FStar_Syntax_Syntax.eff_attrs
                                             in
                                          if uu____13171
                                          then
                                            let uu____13182 =
                                              let uu____13191 =
                                                FStar_TypeChecker_Cfg.embed_simple
                                                  FStar_Syntax_Embeddings.e_range
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____13191
                                               in
                                            let uu____13192 =
                                              let uu____13203 =
                                                let uu____13212 =
                                                  FStar_TypeChecker_Cfg.embed_simple
                                                    FStar_Syntax_Embeddings.e_range
                                                    body2.FStar_Syntax_Syntax.pos
                                                    body2.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Syntax_Syntax.as_arg
                                                  uu____13212
                                                 in
                                              [uu____13203]  in
                                            uu____13182 :: uu____13192
                                          else []  in
                                        let reified =
                                          let uu____13249 =
                                            let uu____13256 =
                                              let uu____13257 =
                                                let uu____13274 =
                                                  let uu____13285 =
                                                    let uu____13296 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        lb.FStar_Syntax_Syntax.lbtyp
                                                       in
                                                    let uu____13305 =
                                                      let uu____13316 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          t
                                                         in
                                                      [uu____13316]  in
                                                    uu____13296 ::
                                                      uu____13305
                                                     in
                                                  let uu____13349 =
                                                    let uu____13360 =
                                                      let uu____13371 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          FStar_Syntax_Syntax.tun
                                                         in
                                                      let uu____13380 =
                                                        let uu____13391 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            head4
                                                           in
                                                        let uu____13400 =
                                                          let uu____13411 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          let uu____13420 =
                                                            let uu____13431 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                body2
                                                               in
                                                            [uu____13431]  in
                                                          uu____13411 ::
                                                            uu____13420
                                                           in
                                                        uu____13391 ::
                                                          uu____13400
                                                         in
                                                      uu____13371 ::
                                                        uu____13380
                                                       in
                                                    FStar_List.append
                                                      maybe_range_arg
                                                      uu____13360
                                                     in
                                                  FStar_List.append
                                                    uu____13285 uu____13349
                                                   in
                                                (bind_inst, uu____13274)  in
                                              FStar_Syntax_Syntax.Tm_app
                                                uu____13257
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____13256
                                             in
                                          uu____13249
                                            FStar_Pervasives_Native.None rng
                                           in
                                        FStar_TypeChecker_Cfg.log cfg
                                          (fun uu____13515  ->
                                             let uu____13516 =
                                               FStar_Syntax_Print.term_to_string
                                                 head0
                                                in
                                             let uu____13517 =
                                               FStar_Syntax_Print.term_to_string
                                                 reified
                                                in
                                             FStar_Util.print2
                                               "Reified (1) <%s> to %s\n"
                                               uu____13516 uu____13517);
                                        (let uu____13518 =
                                           FStar_List.tl stack  in
                                         norm cfg env uu____13518 reified)))))
                  | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                      ((let uu____13546 = FStar_Options.defensive ()  in
                        if uu____13546
                        then
                          let is_arg_impure uu____13558 =
                            match uu____13558 with
                            | (e,q) ->
                                let uu____13571 =
                                  let uu____13572 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____13572.FStar_Syntax_Syntax.n  in
                                (match uu____13571 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____13587 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____13587
                                 | uu____13588 -> false)
                             in
                          let uu____13589 =
                            let uu____13590 =
                              let uu____13601 =
                                FStar_Syntax_Syntax.as_arg head_app  in
                              uu____13601 :: args  in
                            FStar_Util.for_some is_arg_impure uu____13590  in
                          (if uu____13589
                           then
                             let uu____13626 =
                               let uu____13631 =
                                 let uu____13632 =
                                   FStar_Syntax_Print.term_to_string head3
                                    in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____13632
                                  in
                               (FStar_Errors.Warning_Defensive, uu____13631)
                                in
                             FStar_Errors.log_issue
                               head3.FStar_Syntax_Syntax.pos uu____13626
                           else ())
                        else ());
                       (let fallback1 uu____13640 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____13644  ->
                               let uu____13645 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____13645 "");
                          (let uu____13646 = FStar_List.tl stack  in
                           let uu____13647 = FStar_Syntax_Util.mk_reify head3
                              in
                           norm cfg env uu____13646 uu____13647)
                           in
                        let fallback2 uu____13653 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____13657  ->
                               let uu____13658 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____13658 "");
                          (let uu____13659 = FStar_List.tl stack  in
                           let uu____13660 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (head3,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               head0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env uu____13659 uu____13660)
                           in
                        let uu____13665 =
                          let uu____13666 =
                            FStar_Syntax_Util.un_uinst head_app  in
                          uu____13666.FStar_Syntax_Syntax.n  in
                        match uu____13665 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____13672 =
                              let uu____13673 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____13673  in
                            if uu____13672
                            then fallback1 ()
                            else
                              (let uu____13675 =
                                 let uu____13676 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____13676  in
                               if uu____13675
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____13691 =
                                      let uu____13696 =
                                        FStar_Syntax_Util.mk_reify head_app
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____13696 args
                                       in
                                    uu____13691 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____13699 = FStar_List.tl stack  in
                                  norm cfg env uu____13699 t1))
                        | uu____13700 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____13702) ->
                      do_reify_monadic fallback cfg env stack e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____13726 = closure_as_term cfg env t'  in
                        reify_lift cfg e msrc mtgt uu____13726  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____13730  ->
                            let uu____13731 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____13731);
                       (let uu____13732 = FStar_List.tl stack  in
                        norm cfg env uu____13732 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                      let branches1 =
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun uu____13853  ->
                                match uu____13853 with
                                | (pat,wopt,tm) ->
                                    let uu____13901 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____13901)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                          head3.FStar_Syntax_Syntax.pos
                         in
                      let uu____13933 = FStar_List.tl stack  in
                      norm cfg env uu____13933 tm
                  | uu____13934 -> fallback ()))

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
              (fun uu____13948  ->
                 let uu____13949 = FStar_Ident.string_of_lid msrc  in
                 let uu____13950 = FStar_Ident.string_of_lid mtgt  in
                 let uu____13951 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____13949
                   uu____13950 uu____13951);
            (let uu____13952 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____13952
             then
               let ed =
                 let uu____13954 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____13954  in
               let uu____13955 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____13955 with
               | (uu____13956,return_repr) ->
                   let return_inst =
                     let uu____13969 =
                       let uu____13970 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____13970.FStar_Syntax_Syntax.n  in
                     match uu____13969 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____13976::[]) ->
                         let uu____13981 =
                           let uu____13988 =
                             let uu____13989 =
                               let uu____13996 =
                                 let uu____13997 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____13997]  in
                               (return_tm, uu____13996)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____13989  in
                           FStar_Syntax_Syntax.mk uu____13988  in
                         uu____13981 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____14003 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____14006 =
                     let uu____14013 =
                       let uu____14014 =
                         let uu____14031 =
                           let uu____14042 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____14051 =
                             let uu____14062 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____14062]  in
                           uu____14042 :: uu____14051  in
                         (return_inst, uu____14031)  in
                       FStar_Syntax_Syntax.Tm_app uu____14014  in
                     FStar_Syntax_Syntax.mk uu____14013  in
                   uu____14006 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____14111 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____14111 with
                | FStar_Pervasives_Native.None  ->
                    let uu____14114 =
                      let uu____14115 = FStar_Ident.text_of_lid msrc  in
                      let uu____14116 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____14115 uu____14116
                       in
                    failwith uu____14114
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14117;
                      FStar_TypeChecker_Env.mtarget = uu____14118;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14119;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____14141 =
                      let uu____14142 = FStar_Ident.text_of_lid msrc  in
                      let uu____14143 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____14142 uu____14143
                       in
                    failwith uu____14141
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14144;
                      FStar_TypeChecker_Env.mtarget = uu____14145;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14146;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____14181 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____14182 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____14181 t FStar_Syntax_Syntax.tun uu____14182))

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
                (fun uu____14252  ->
                   match uu____14252 with
                   | (a,imp) ->
                       let uu____14271 = norm cfg env [] a  in
                       (uu____14271, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____14281  ->
             let uu____14282 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____14283 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____14282 uu____14283);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____14307 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____14307
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___321_14310 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___321_14310.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___321_14310.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____14332 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____14332
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___322_14335 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___322_14335.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___322_14335.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____14380  ->
                      match uu____14380 with
                      | (a,i) ->
                          let uu____14399 = norm cfg env [] a  in
                          (uu____14399, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___266_14421  ->
                       match uu___266_14421 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____14425 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____14425
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___323_14433 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___324_14436 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___324_14436.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___323_14433.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___323_14433.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun b  ->
        let uu____14440 = b  in
        match uu____14440 with
        | (x,imp) ->
            let x1 =
              let uu___325_14448 = x  in
              let uu____14449 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___325_14448.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___325_14448.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____14449
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____14460 =
                    let uu____14461 = closure_as_term cfg env t  in
                    FStar_Syntax_Syntax.Meta uu____14461  in
                  FStar_Pervasives_Native.Some uu____14460
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____14472 =
          FStar_List.fold_left
            (fun uu____14506  ->
               fun b  ->
                 match uu____14506 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____14472 with | (nbs,uu____14586) -> FStar_List.rev nbs

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
            let uu____14618 =
              let uu___326_14619 = rc  in
              let uu____14620 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___326_14619.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____14620;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___326_14619.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____14618
        | uu____14629 -> lopt

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
            (let uu____14638 = FStar_Syntax_Print.term_to_string tm  in
             let uu____14639 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____14638 uu____14639)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___267_14643  ->
      match uu___267_14643 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____14656 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____14656 with
           | FStar_Pervasives_Native.Some (t,uu____14664) -> t
           | FStar_Pervasives_Native.None  ->
               let uu____14673 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____14673)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____14681 = norm_cb cfg  in
            reduce_primops uu____14681 cfg env tm  in
          let uu____14688 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____14688
          then tm1
          else
            (let w t =
               let uu___327_14702 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___327_14702.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___327_14702.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____14713 =
                 let uu____14714 = FStar_Syntax_Util.unmeta t  in
                 uu____14714.FStar_Syntax_Syntax.n  in
               match uu____14713 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____14721 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____14782)::args1,(bv,uu____14785)::bs1) ->
                   let uu____14839 =
                     let uu____14840 = FStar_Syntax_Subst.compress t  in
                     uu____14840.FStar_Syntax_Syntax.n  in
                   (match uu____14839 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____14844 -> false)
               | ([],[]) -> true
               | (uu____14873,uu____14874) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____14923 = FStar_Syntax_Print.term_to_string t  in
                  let uu____14924 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____14923
                    uu____14924)
               else ();
               (let uu____14926 = FStar_Syntax_Util.head_and_args' t  in
                match uu____14926 with
                | (hd1,args) ->
                    let uu____14965 =
                      let uu____14966 = FStar_Syntax_Subst.compress hd1  in
                      uu____14966.FStar_Syntax_Syntax.n  in
                    (match uu____14965 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____14973 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____14974 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____14975 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____14973 uu____14974 uu____14975)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____14977 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____14994 = FStar_Syntax_Print.term_to_string t  in
                  let uu____14995 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____14994
                    uu____14995)
               else ();
               (let uu____14997 = FStar_Syntax_Util.is_squash t  in
                match uu____14997 with
                | FStar_Pervasives_Native.Some (uu____15008,t') ->
                    is_applied bs t'
                | uu____15020 ->
                    let uu____15029 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____15029 with
                     | FStar_Pervasives_Native.Some (uu____15040,t') ->
                         is_applied bs t'
                     | uu____15052 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____15076 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____15076 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____15083)::(q,uu____15085)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____15127 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____15128 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____15127 uu____15128)
                    else ();
                    (let uu____15130 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____15130 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____15135 =
                           let uu____15136 = FStar_Syntax_Subst.compress p
                              in
                           uu____15136.FStar_Syntax_Syntax.n  in
                         (match uu____15135 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____15144 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____15144))
                          | uu____15147 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____15150)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____15175 =
                           let uu____15176 = FStar_Syntax_Subst.compress p1
                              in
                           uu____15176.FStar_Syntax_Syntax.n  in
                         (match uu____15175 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____15184 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____15184))
                          | uu____15187 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____15191 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____15191 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____15196 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____15196 with
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
                                     let uu____15207 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____15207))
                               | uu____15210 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____15215)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____15240 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____15240 with
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
                                     let uu____15251 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____15251))
                               | uu____15254 -> FStar_Pervasives_Native.None)
                          | uu____15257 -> FStar_Pervasives_Native.None)
                     | uu____15260 -> FStar_Pervasives_Native.None))
               | uu____15263 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____15276 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____15276 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____15282)::[],uu____15283,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____15302 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____15303 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____15302
                         uu____15303)
                    else ();
                    is_quantified_const bv phi')
               | uu____15305 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____15318 =
                 let uu____15319 = FStar_Syntax_Subst.compress phi  in
                 uu____15319.FStar_Syntax_Syntax.n  in
               match uu____15318 with
               | FStar_Syntax_Syntax.Tm_match (uu____15324,br::brs) ->
                   let uu____15391 = br  in
                   (match uu____15391 with
                    | (uu____15408,uu____15409,e) ->
                        let r =
                          let uu____15430 = simp_t e  in
                          match uu____15430 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____15436 =
                                FStar_List.for_all
                                  (fun uu____15454  ->
                                     match uu____15454 with
                                     | (uu____15467,uu____15468,e') ->
                                         let uu____15482 = simp_t e'  in
                                         uu____15482 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____15436
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____15490 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____15499 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____15499
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____15534 =
                 match uu____15534 with
                 | (t1,q) ->
                     let uu____15555 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____15555 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____15587 -> (t1, q))
                  in
               let uu____15600 = FStar_Syntax_Util.head_and_args t  in
               match uu____15600 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____15678 =
                 let uu____15679 = FStar_Syntax_Util.unmeta ty  in
                 uu____15679.FStar_Syntax_Syntax.n  in
               match uu____15678 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____15683) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____15688,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____15712 -> false  in
             let simplify1 arg =
               let uu____15743 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____15743, arg)  in
             let uu____15756 = is_forall_const tm1  in
             match uu____15756 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____15761 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____15762 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____15761
                       uu____15762)
                  else ();
                  (let uu____15764 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____15764))
             | FStar_Pervasives_Native.None  ->
                 let uu____15765 =
                   let uu____15766 = FStar_Syntax_Subst.compress tm1  in
                   uu____15766.FStar_Syntax_Syntax.n  in
                 (match uu____15765 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____15770;
                              FStar_Syntax_Syntax.vars = uu____15771;_},uu____15772);
                         FStar_Syntax_Syntax.pos = uu____15773;
                         FStar_Syntax_Syntax.vars = uu____15774;_},args)
                      ->
                      let uu____15804 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____15804
                      then
                        let uu____15805 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____15805 with
                         | (FStar_Pervasives_Native.Some (true ),uu____15860)::
                             (uu____15861,(arg,uu____15863))::[] ->
                             maybe_auto_squash arg
                         | (uu____15928,(arg,uu____15930))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____15931)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____15996)::uu____15997::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____16060::(FStar_Pervasives_Native.Some (false
                                         ),uu____16061)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____16124 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____16140 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____16140
                         then
                           let uu____16141 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____16141 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____16196)::uu____16197::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____16260::(FStar_Pervasives_Native.Some (true
                                           ),uu____16261)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____16324)::(uu____16325,(arg,uu____16327))::[]
                               -> maybe_auto_squash arg
                           | (uu____16392,(arg,uu____16394))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____16395)::[]
                               -> maybe_auto_squash arg
                           | uu____16460 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____16476 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____16476
                            then
                              let uu____16477 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____16477 with
                              | uu____16532::(FStar_Pervasives_Native.Some
                                              (true ),uu____16533)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____16596)::uu____16597::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____16660)::(uu____16661,(arg,uu____16663))::[]
                                  -> maybe_auto_squash arg
                              | (uu____16728,(p,uu____16730))::(uu____16731,
                                                                (q,uu____16733))::[]
                                  ->
                                  let uu____16798 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____16798
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____16800 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____16816 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____16816
                               then
                                 let uu____16817 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____16817 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16872)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____16873)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____16938)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____16939)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17004)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____17005)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17070)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17071)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____17136,(arg,uu____17138))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____17139)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17204)::(uu____17205,(arg,uu____17207))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____17272,(arg,uu____17274))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____17275)::[]
                                     ->
                                     let uu____17340 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17340
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17341)::(uu____17342,(arg,uu____17344))::[]
                                     ->
                                     let uu____17409 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17409
                                 | (uu____17410,(p,uu____17412))::(uu____17413,
                                                                   (q,uu____17415))::[]
                                     ->
                                     let uu____17480 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____17480
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____17482 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____17498 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____17498
                                  then
                                    let uu____17499 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____17499 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____17554)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____17593)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____17632 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____17648 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____17648
                                     then
                                       match args with
                                       | (t,uu____17650)::[] ->
                                           let uu____17675 =
                                             let uu____17676 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17676.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17675 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17679::[],body,uu____17681)
                                                ->
                                                let uu____17716 = simp_t body
                                                   in
                                                (match uu____17716 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____17719 -> tm1)
                                            | uu____17722 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____17724))::(t,uu____17726)::[]
                                           ->
                                           let uu____17765 =
                                             let uu____17766 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17766.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17765 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17769::[],body,uu____17771)
                                                ->
                                                let uu____17806 = simp_t body
                                                   in
                                                (match uu____17806 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____17809 -> tm1)
                                            | uu____17812 -> tm1)
                                       | uu____17813 -> tm1
                                     else
                                       (let uu____17825 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____17825
                                        then
                                          match args with
                                          | (t,uu____17827)::[] ->
                                              let uu____17852 =
                                                let uu____17853 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17853.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17852 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17856::[],body,uu____17858)
                                                   ->
                                                   let uu____17893 =
                                                     simp_t body  in
                                                   (match uu____17893 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____17896 -> tm1)
                                               | uu____17899 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____17901))::(t,uu____17903)::[]
                                              ->
                                              let uu____17942 =
                                                let uu____17943 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17943.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17942 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17946::[],body,uu____17948)
                                                   ->
                                                   let uu____17983 =
                                                     simp_t body  in
                                                   (match uu____17983 with
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
                                                    | uu____17986 -> tm1)
                                               | uu____17989 -> tm1)
                                          | uu____17990 -> tm1
                                        else
                                          (let uu____18002 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____18002
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18003;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18004;_},uu____18005)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18030;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18031;_},uu____18032)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____18057 -> tm1
                                           else
                                             (let uu____18069 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____18069 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____18089 ->
                                                  let uu____18098 =
                                                    let uu____18105 =
                                                      norm_cb cfg  in
                                                    reduce_equality
                                                      uu____18105 cfg env
                                                     in
                                                  uu____18098 tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____18113;
                         FStar_Syntax_Syntax.vars = uu____18114;_},args)
                      ->
                      let uu____18140 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18140
                      then
                        let uu____18141 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18141 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18196)::
                             (uu____18197,(arg,uu____18199))::[] ->
                             maybe_auto_squash arg
                         | (uu____18264,(arg,uu____18266))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18267)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18332)::uu____18333::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18396::(FStar_Pervasives_Native.Some (false
                                         ),uu____18397)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18460 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18476 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18476
                         then
                           let uu____18477 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18477 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18532)::uu____18533::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18596::(FStar_Pervasives_Native.Some (true
                                           ),uu____18597)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18660)::(uu____18661,(arg,uu____18663))::[]
                               -> maybe_auto_squash arg
                           | (uu____18728,(arg,uu____18730))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18731)::[]
                               -> maybe_auto_squash arg
                           | uu____18796 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18812 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____18812
                            then
                              let uu____18813 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____18813 with
                              | uu____18868::(FStar_Pervasives_Native.Some
                                              (true ),uu____18869)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____18932)::uu____18933::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____18996)::(uu____18997,(arg,uu____18999))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19064,(p,uu____19066))::(uu____19067,
                                                                (q,uu____19069))::[]
                                  ->
                                  let uu____19134 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19134
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19136 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19152 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19152
                               then
                                 let uu____19153 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19153 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19208)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19209)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19274)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19275)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19340)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19341)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19406)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19407)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19472,(arg,uu____19474))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19475)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19540)::(uu____19541,(arg,uu____19543))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19608,(arg,uu____19610))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19611)::[]
                                     ->
                                     let uu____19676 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19676
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19677)::(uu____19678,(arg,uu____19680))::[]
                                     ->
                                     let uu____19745 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19745
                                 | (uu____19746,(p,uu____19748))::(uu____19749,
                                                                   (q,uu____19751))::[]
                                     ->
                                     let uu____19816 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19816
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19818 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19834 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19834
                                  then
                                    let uu____19835 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19835 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19890)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19929)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19968 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19984 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19984
                                     then
                                       match args with
                                       | (t,uu____19986)::[] ->
                                           let uu____20011 =
                                             let uu____20012 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20012.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20011 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20015::[],body,uu____20017)
                                                ->
                                                let uu____20052 = simp_t body
                                                   in
                                                (match uu____20052 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20055 -> tm1)
                                            | uu____20058 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20060))::(t,uu____20062)::[]
                                           ->
                                           let uu____20101 =
                                             let uu____20102 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20102.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20101 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20105::[],body,uu____20107)
                                                ->
                                                let uu____20142 = simp_t body
                                                   in
                                                (match uu____20142 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20145 -> tm1)
                                            | uu____20148 -> tm1)
                                       | uu____20149 -> tm1
                                     else
                                       (let uu____20161 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20161
                                        then
                                          match args with
                                          | (t,uu____20163)::[] ->
                                              let uu____20188 =
                                                let uu____20189 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20189.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20188 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20192::[],body,uu____20194)
                                                   ->
                                                   let uu____20229 =
                                                     simp_t body  in
                                                   (match uu____20229 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20232 -> tm1)
                                               | uu____20235 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20237))::(t,uu____20239)::[]
                                              ->
                                              let uu____20278 =
                                                let uu____20279 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20279.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20278 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20282::[],body,uu____20284)
                                                   ->
                                                   let uu____20319 =
                                                     simp_t body  in
                                                   (match uu____20319 with
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
                                                    | uu____20322 -> tm1)
                                               | uu____20325 -> tm1)
                                          | uu____20326 -> tm1
                                        else
                                          (let uu____20338 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20338
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20339;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20340;_},uu____20341)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20366;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20367;_},uu____20368)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20393 -> tm1
                                           else
                                             (let uu____20405 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20405 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20425 ->
                                                  let uu____20434 =
                                                    let uu____20441 =
                                                      norm_cb cfg  in
                                                    reduce_equality
                                                      uu____20441 cfg env
                                                     in
                                                  uu____20434 tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____20454 = simp_t t  in
                      (match uu____20454 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____20457 ->
                      let uu____20480 = is_const_match tm1  in
                      (match uu____20480 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____20483 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____20493  ->
               (let uu____20495 = FStar_Syntax_Print.tag_of_term t  in
                let uu____20496 = FStar_Syntax_Print.term_to_string t  in
                let uu____20497 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____20504 =
                  let uu____20505 =
                    let uu____20508 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____20508
                     in
                  stack_to_string uu____20505  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____20495 uu____20496 uu____20497 uu____20504);
               (let uu____20531 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____20531
                then
                  let uu____20532 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____20532 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____20539 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____20540 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____20541 =
                          let uu____20542 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____20542
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____20539
                          uu____20540 uu____20541);
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
                   let uu____20560 =
                     let uu____20561 =
                       let uu____20562 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____20562  in
                     FStar_Util.string_of_int uu____20561  in
                   let uu____20567 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____20568 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____20560 uu____20567 uu____20568)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____20574,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                FStar_TypeChecker_Cfg.log cfg
                  (fun uu____20625  ->
                     let uu____20626 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____20626);
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
               let uu____20664 =
                 let uu___328_20665 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___328_20665.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___328_20665.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____20664
           | (Arg (Univ uu____20668,uu____20669,uu____20670))::uu____20671 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____20674,uu____20675))::uu____20676 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____20691,uu____20692),aq,r))::stack1
               when
               let uu____20742 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____20742 ->
               let t2 =
                 let uu____20746 =
                   let uu____20751 =
                     let uu____20752 = closure_as_term cfg env_arg tm  in
                     (uu____20752, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____20751  in
                 uu____20746 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____20764),aq,r))::stack1 ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____20817  ->
                     let uu____20818 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____20818);
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
                  (let uu____20832 = FStar_ST.op_Bang m  in
                   match uu____20832 with
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
                   | FStar_Pervasives_Native.Some (uu____20973,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____21028 =
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____21032  ->
                      let uu____21033 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____21033);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____21041 =
                 let uu____21042 = FStar_Syntax_Subst.compress t1  in
                 uu____21042.FStar_Syntax_Syntax.n  in
               (match uu____21041 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____21069 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____21069  in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____21073  ->
                          let uu____21074 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____21074);
                     (let uu____21075 = FStar_List.tl stack  in
                      norm cfg env1 uu____21075 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____21076);
                       FStar_Syntax_Syntax.pos = uu____21077;
                       FStar_Syntax_Syntax.vars = uu____21078;_},(e,uu____21080)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____21119 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                    ->
                    let uu____21136 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____21136 with
                     | (hd1,args) ->
                         let uu____21179 =
                           let uu____21180 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____21180.FStar_Syntax_Syntax.n  in
                         (match uu____21179 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____21184 =
                                FStar_TypeChecker_Cfg.find_prim_step cfg fv
                                 in
                              (match uu____21184 with
                               | FStar_Pervasives_Native.Some
                                   {
                                     FStar_TypeChecker_Cfg.name = uu____21187;
                                     FStar_TypeChecker_Cfg.arity =
                                       uu____21188;
                                     FStar_TypeChecker_Cfg.univ_arity =
                                       uu____21189;
                                     FStar_TypeChecker_Cfg.auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     FStar_TypeChecker_Cfg.strong_reduction_ok
                                       = uu____21191;
                                     FStar_TypeChecker_Cfg.requires_binder_substitution
                                       = uu____21192;
                                     FStar_TypeChecker_Cfg.interpretation =
                                       uu____21193;
                                     FStar_TypeChecker_Cfg.interpretation_nbe
                                       = uu____21194;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____21224 -> fallback " (3)" ())
                          | uu____21227 -> fallback " (4)" ()))
                | uu____21228 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (FStar_TypeChecker_Cfg.log cfg1
                  (fun uu____21253  ->
                     let uu____21254 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____21254);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____21263 =
                   FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____21268  ->
                        let uu____21269 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____21270 =
                          let uu____21271 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____21298  ->
                                    match uu____21298 with
                                    | (p,uu____21308,uu____21309) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____21271
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____21269 uu____21270);
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
                             (fun uu___268_21326  ->
                                match uu___268_21326 with
                                | FStar_TypeChecker_Env.InliningDelta  ->
                                    true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____21327 -> false))
                         in
                      let steps =
                        let uu___329_21329 = cfg1.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___329_21329.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___329_21329.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta = false;
                          FStar_TypeChecker_Cfg.weak =
                            (uu___329_21329.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___329_21329.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___329_21329.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___329_21329.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___329_21329.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_tac = false;
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___329_21329.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___329_21329.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___329_21329.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___329_21329.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___329_21329.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___329_21329.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___329_21329.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___329_21329.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___329_21329.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___329_21329.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___329_21329.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___329_21329.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___329_21329.FStar_TypeChecker_Cfg.nbe_step)
                        }  in
                      let uu___330_21334 = cfg1  in
                      {
                        FStar_TypeChecker_Cfg.steps = steps;
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___330_21334.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___330_21334.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level = new_delta;
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___330_21334.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong = true;
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___330_21334.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___330_21334.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying =
                          (uu___330_21334.FStar_TypeChecker_Cfg.reifying)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____21406 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____21435 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____21519  ->
                                    fun uu____21520  ->
                                      match (uu____21519, uu____21520) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____21659 = norm_pat env3 p1
                                             in
                                          (match uu____21659 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____21435 with
                           | (pats1,env3) ->
                               ((let uu___331_21821 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___331_21821.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___332_21840 = x  in
                            let uu____21841 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___332_21840.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___332_21840.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21841
                            }  in
                          ((let uu___333_21855 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___333_21855.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___334_21866 = x  in
                            let uu____21867 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___334_21866.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___334_21866.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21867
                            }  in
                          ((let uu___335_21881 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___335_21881.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___336_21897 = x  in
                            let uu____21898 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___336_21897.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___336_21897.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21898
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___337_21913 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___337_21913.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____21957 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____21987 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____21987 with
                                  | (p,wopt,e) ->
                                      let uu____22007 = norm_pat env1 p  in
                                      (match uu____22007 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____22062 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____22062
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____22079 =
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
                      if uu____22079
                      then
                        norm
                          (let uu___338_22084 = cfg1  in
                           {
                             FStar_TypeChecker_Cfg.steps =
                               (let uu___339_22087 =
                                  cfg1.FStar_TypeChecker_Cfg.steps  in
                                {
                                  FStar_TypeChecker_Cfg.beta =
                                    (uu___339_22087.FStar_TypeChecker_Cfg.beta);
                                  FStar_TypeChecker_Cfg.iota =
                                    (uu___339_22087.FStar_TypeChecker_Cfg.iota);
                                  FStar_TypeChecker_Cfg.zeta =
                                    (uu___339_22087.FStar_TypeChecker_Cfg.zeta);
                                  FStar_TypeChecker_Cfg.weak =
                                    (uu___339_22087.FStar_TypeChecker_Cfg.weak);
                                  FStar_TypeChecker_Cfg.hnf =
                                    (uu___339_22087.FStar_TypeChecker_Cfg.hnf);
                                  FStar_TypeChecker_Cfg.primops =
                                    (uu___339_22087.FStar_TypeChecker_Cfg.primops);
                                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                    =
                                    (uu___339_22087.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                  FStar_TypeChecker_Cfg.unfold_until =
                                    (uu___339_22087.FStar_TypeChecker_Cfg.unfold_until);
                                  FStar_TypeChecker_Cfg.unfold_only =
                                    (uu___339_22087.FStar_TypeChecker_Cfg.unfold_only);
                                  FStar_TypeChecker_Cfg.unfold_fully =
                                    (uu___339_22087.FStar_TypeChecker_Cfg.unfold_fully);
                                  FStar_TypeChecker_Cfg.unfold_attr =
                                    (uu___339_22087.FStar_TypeChecker_Cfg.unfold_attr);
                                  FStar_TypeChecker_Cfg.unfold_tac =
                                    (uu___339_22087.FStar_TypeChecker_Cfg.unfold_tac);
                                  FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                    =
                                    (uu___339_22087.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                  FStar_TypeChecker_Cfg.simplify =
                                    (uu___339_22087.FStar_TypeChecker_Cfg.simplify);
                                  FStar_TypeChecker_Cfg.erase_universes =
                                    (uu___339_22087.FStar_TypeChecker_Cfg.erase_universes);
                                  FStar_TypeChecker_Cfg.allow_unbound_universes
                                    =
                                    (uu___339_22087.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                  FStar_TypeChecker_Cfg.reify_ =
                                    (uu___339_22087.FStar_TypeChecker_Cfg.reify_);
                                  FStar_TypeChecker_Cfg.compress_uvars =
                                    (uu___339_22087.FStar_TypeChecker_Cfg.compress_uvars);
                                  FStar_TypeChecker_Cfg.no_full_norm =
                                    (uu___339_22087.FStar_TypeChecker_Cfg.no_full_norm);
                                  FStar_TypeChecker_Cfg.check_no_uvars =
                                    (uu___339_22087.FStar_TypeChecker_Cfg.check_no_uvars);
                                  FStar_TypeChecker_Cfg.unmeta =
                                    (uu___339_22087.FStar_TypeChecker_Cfg.unmeta);
                                  FStar_TypeChecker_Cfg.unascribe =
                                    (uu___339_22087.FStar_TypeChecker_Cfg.unascribe);
                                  FStar_TypeChecker_Cfg.in_full_norm_request
                                    =
                                    (uu___339_22087.FStar_TypeChecker_Cfg.in_full_norm_request);
                                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                    = false;
                                  FStar_TypeChecker_Cfg.nbe_step =
                                    (uu___339_22087.FStar_TypeChecker_Cfg.nbe_step)
                                });
                             FStar_TypeChecker_Cfg.tcenv =
                               (uu___338_22084.FStar_TypeChecker_Cfg.tcenv);
                             FStar_TypeChecker_Cfg.debug =
                               (uu___338_22084.FStar_TypeChecker_Cfg.debug);
                             FStar_TypeChecker_Cfg.delta_level =
                               (uu___338_22084.FStar_TypeChecker_Cfg.delta_level);
                             FStar_TypeChecker_Cfg.primitive_steps =
                               (uu___338_22084.FStar_TypeChecker_Cfg.primitive_steps);
                             FStar_TypeChecker_Cfg.strong =
                               (uu___338_22084.FStar_TypeChecker_Cfg.strong);
                             FStar_TypeChecker_Cfg.memoize_lazy =
                               (uu___338_22084.FStar_TypeChecker_Cfg.memoize_lazy);
                             FStar_TypeChecker_Cfg.normalize_pure_lets =
                               (uu___338_22084.FStar_TypeChecker_Cfg.normalize_pure_lets);
                             FStar_TypeChecker_Cfg.reifying =
                               (uu___338_22084.FStar_TypeChecker_Cfg.reifying)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____22089 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____22089)
                    in
                 let rec is_cons head1 =
                   let uu____22114 =
                     let uu____22115 = FStar_Syntax_Subst.compress head1  in
                     uu____22115.FStar_Syntax_Syntax.n  in
                   match uu____22114 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____22119) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____22124 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____22125;
                         FStar_Syntax_Syntax.fv_delta = uu____22126;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____22127;
                         FStar_Syntax_Syntax.fv_delta = uu____22128;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____22129);_}
                       -> true
                   | uu____22136 -> false  in
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
                   let uu____22300 =
                     FStar_Syntax_Util.head_and_args scrutinee2  in
                   match uu____22300 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____22393 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee2.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____22432 ->
                                 let uu____22433 =
                                   let uu____22434 = is_cons head1  in
                                   Prims.op_Negation uu____22434  in
                                 FStar_Util.Inr uu____22433)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____22459 =
                              let uu____22460 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____22460.FStar_Syntax_Syntax.n  in
                            (match uu____22459 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____22478 ->
                                 let uu____22479 =
                                   let uu____22480 = is_cons head1  in
                                   Prims.op_Negation uu____22480  in
                                 FStar_Util.Inr uu____22479))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____22563)::rest_a,(p1,uu____22566)::rest_p) ->
                       let uu____22620 = matches_pat t2 p1  in
                       (match uu____22620 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____22669 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____22789 = matches_pat scrutinee1 p1  in
                       (match uu____22789 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (FStar_TypeChecker_Cfg.log cfg1
                               (fun uu____22829  ->
                                  let uu____22830 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____22831 =
                                    let uu____22832 =
                                      FStar_List.map
                                        (fun uu____22842  ->
                                           match uu____22842 with
                                           | (uu____22847,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____22832
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____22830 uu____22831);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____22879  ->
                                       match uu____22879 with
                                       | (bv,t2) ->
                                           let uu____22902 =
                                             let uu____22909 =
                                               let uu____22912 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____22912
                                                in
                                             let uu____22913 =
                                               let uu____22914 =
                                                 let uu____22945 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____22945, false)
                                                  in
                                               Clos uu____22914  in
                                             (uu____22909, uu____22913)  in
                                           uu____22902 :: env2) env1 s
                                 in
                              let uu____23058 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____23058)))
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
            (fun uu____23088  ->
               let uu____23089 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____23089);
          (let uu____23090 = is_nbe_request s  in
           if uu____23090
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____23094  ->
                   let uu____23095 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____23095);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____23099  ->
                   let uu____23100 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____23100);
              (let r = nbe_eval c s t  in
               FStar_TypeChecker_Cfg.log_top c
                 (fun uu____23105  ->
                    let uu____23106 = FStar_Syntax_Print.term_to_string r  in
                    FStar_Util.print1 "}\nNormalization result = (%s)\n"
                      uu____23106);
               r))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____23111  ->
                   let uu____23112 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____23112);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____23116  ->
                   let uu____23117 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____23117);
              (let r = norm c [] [] t  in
               FStar_TypeChecker_Cfg.log_top c
                 (fun uu____23128  ->
                    let uu____23129 = FStar_Syntax_Print.term_to_string r  in
                    FStar_Util.print1 "}\nNormalization result = (%s)\n"
                      uu____23129);
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
        let uu____23160 = FStar_TypeChecker_Cfg.config s e  in
        norm_comp uu____23160 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____23177 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____23177 [] u
  
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
        let uu____23201 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____23201  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____23208 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___340_23227 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___340_23227.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___340_23227.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name
              cfg.FStar_TypeChecker_Cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____23234 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____23234
          then
            let ct1 =
              let uu____23236 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____23236 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____23243 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____23243
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___341_23247 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___341_23247.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___341_23247.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___341_23247.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev
                      cfg.FStar_TypeChecker_Cfg.tcenv c
                     in
                  let uu___342_23249 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___342_23249.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___342_23249.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___342_23249.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___342_23249.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___343_23250 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___343_23250.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___343_23250.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____23252 -> c
  
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
        let uu____23270 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____23270  in
      let uu____23277 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____23277
      then
        let uu____23278 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____23278 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____23284  ->
                 let uu____23285 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____23285)
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
          (fun uu___345_23299  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___344_23302 ->
            ((let uu____23304 =
                let uu____23309 =
                  let uu____23310 = FStar_Util.message_of_exn uu___344_23302
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23310
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____23309)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____23304);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          (fun uu___347_23324  ->
             match () with
             | () ->
                 let uu____23325 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____23325 [] c) ()
        with
        | uu___346_23334 ->
            ((let uu____23336 =
                let uu____23341 =
                  let uu____23342 = FStar_Util.message_of_exn uu___346_23334
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23342
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____23341)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____23336);
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
                   let uu____23387 =
                     let uu____23388 =
                       let uu____23395 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____23395)  in
                     FStar_Syntax_Syntax.Tm_refine uu____23388  in
                   mk uu____23387 t01.FStar_Syntax_Syntax.pos
               | uu____23400 -> t2)
          | uu____23401 -> t2  in
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
        let uu____23482 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____23482 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____23519 ->
                 let uu____23528 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____23528 with
                  | (actuals,uu____23538,uu____23539) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____23557 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____23557 with
                         | (binders,args) ->
                             let uu____23568 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____23568
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
      | uu____23582 ->
          let uu____23583 = FStar_Syntax_Util.head_and_args t  in
          (match uu____23583 with
           | (head1,args) ->
               let uu____23626 =
                 let uu____23627 = FStar_Syntax_Subst.compress head1  in
                 uu____23627.FStar_Syntax_Syntax.n  in
               (match uu____23626 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____23648 =
                      let uu____23663 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____23663  in
                    (match uu____23648 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____23701 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___348_23709 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___348_23709.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___348_23709.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___348_23709.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___348_23709.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___348_23709.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___348_23709.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___348_23709.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___348_23709.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___348_23709.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___348_23709.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___348_23709.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___348_23709.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___348_23709.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___348_23709.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___348_23709.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___348_23709.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___348_23709.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___348_23709.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___348_23709.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___348_23709.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___348_23709.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___348_23709.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___348_23709.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___348_23709.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___348_23709.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___348_23709.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___348_23709.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___348_23709.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___348_23709.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___348_23709.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___348_23709.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___348_23709.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___348_23709.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___348_23709.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___348_23709.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___348_23709.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___348_23709.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___348_23709.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___348_23709.FStar_TypeChecker_Env.nbe)
                                 }) t
                               in
                            match uu____23701 with
                            | (uu____23710,ty,uu____23712) ->
                                eta_expand_with_type env t ty))
                | uu____23713 ->
                    let uu____23714 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___349_23722 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___349_23722.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___349_23722.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___349_23722.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___349_23722.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___349_23722.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___349_23722.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___349_23722.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___349_23722.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___349_23722.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___349_23722.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___349_23722.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___349_23722.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___349_23722.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___349_23722.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___349_23722.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___349_23722.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___349_23722.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___349_23722.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___349_23722.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___349_23722.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___349_23722.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___349_23722.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___349_23722.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___349_23722.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___349_23722.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___349_23722.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___349_23722.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___349_23722.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___349_23722.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___349_23722.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___349_23722.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___349_23722.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___349_23722.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___349_23722.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___349_23722.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___349_23722.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___349_23722.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___349_23722.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___349_23722.FStar_TypeChecker_Env.nbe)
                         }) t
                       in
                    (match uu____23714 with
                     | (uu____23723,ty,uu____23725) ->
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
      let uu___350_23806 = x  in
      let uu____23807 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___350_23806.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___350_23806.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____23807
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____23810 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____23833 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____23834 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____23835 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____23836 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____23843 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____23844 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____23845 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___351_23879 = rc  in
          let uu____23880 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____23889 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___351_23879.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____23880;
            FStar_Syntax_Syntax.residual_flags = uu____23889
          }  in
        let uu____23892 =
          let uu____23893 =
            let uu____23912 = elim_delayed_subst_binders bs  in
            let uu____23921 = elim_delayed_subst_term t2  in
            let uu____23924 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____23912, uu____23921, uu____23924)  in
          FStar_Syntax_Syntax.Tm_abs uu____23893  in
        mk1 uu____23892
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____23961 =
          let uu____23962 =
            let uu____23977 = elim_delayed_subst_binders bs  in
            let uu____23986 = elim_delayed_subst_comp c  in
            (uu____23977, uu____23986)  in
          FStar_Syntax_Syntax.Tm_arrow uu____23962  in
        mk1 uu____23961
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____24005 =
          let uu____24006 =
            let uu____24013 = elim_bv bv  in
            let uu____24014 = elim_delayed_subst_term phi  in
            (uu____24013, uu____24014)  in
          FStar_Syntax_Syntax.Tm_refine uu____24006  in
        mk1 uu____24005
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____24045 =
          let uu____24046 =
            let uu____24063 = elim_delayed_subst_term t2  in
            let uu____24066 = elim_delayed_subst_args args  in
            (uu____24063, uu____24066)  in
          FStar_Syntax_Syntax.Tm_app uu____24046  in
        mk1 uu____24045
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___352_24138 = p  in
              let uu____24139 =
                let uu____24140 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____24140  in
              {
                FStar_Syntax_Syntax.v = uu____24139;
                FStar_Syntax_Syntax.p =
                  (uu___352_24138.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___353_24142 = p  in
              let uu____24143 =
                let uu____24144 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____24144  in
              {
                FStar_Syntax_Syntax.v = uu____24143;
                FStar_Syntax_Syntax.p =
                  (uu___353_24142.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___354_24151 = p  in
              let uu____24152 =
                let uu____24153 =
                  let uu____24160 = elim_bv x  in
                  let uu____24161 = elim_delayed_subst_term t0  in
                  (uu____24160, uu____24161)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____24153  in
              {
                FStar_Syntax_Syntax.v = uu____24152;
                FStar_Syntax_Syntax.p =
                  (uu___354_24151.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___355_24184 = p  in
              let uu____24185 =
                let uu____24186 =
                  let uu____24199 =
                    FStar_List.map
                      (fun uu____24222  ->
                         match uu____24222 with
                         | (x,b) ->
                             let uu____24235 = elim_pat x  in
                             (uu____24235, b)) pats
                     in
                  (fv, uu____24199)  in
                FStar_Syntax_Syntax.Pat_cons uu____24186  in
              {
                FStar_Syntax_Syntax.v = uu____24185;
                FStar_Syntax_Syntax.p =
                  (uu___355_24184.FStar_Syntax_Syntax.p)
              }
          | uu____24248 -> p  in
        let elim_branch uu____24272 =
          match uu____24272 with
          | (pat,wopt,t3) ->
              let uu____24298 = elim_pat pat  in
              let uu____24301 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____24304 = elim_delayed_subst_term t3  in
              (uu____24298, uu____24301, uu____24304)
           in
        let uu____24309 =
          let uu____24310 =
            let uu____24333 = elim_delayed_subst_term t2  in
            let uu____24336 = FStar_List.map elim_branch branches  in
            (uu____24333, uu____24336)  in
          FStar_Syntax_Syntax.Tm_match uu____24310  in
        mk1 uu____24309
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____24467 =
          match uu____24467 with
          | (tc,topt) ->
              let uu____24502 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____24512 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____24512
                | FStar_Util.Inr c ->
                    let uu____24514 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____24514
                 in
              let uu____24515 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____24502, uu____24515)
           in
        let uu____24524 =
          let uu____24525 =
            let uu____24552 = elim_delayed_subst_term t2  in
            let uu____24555 = elim_ascription a  in
            (uu____24552, uu____24555, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____24525  in
        mk1 uu____24524
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___356_24616 = lb  in
          let uu____24617 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____24620 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___356_24616.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___356_24616.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____24617;
            FStar_Syntax_Syntax.lbeff =
              (uu___356_24616.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____24620;
            FStar_Syntax_Syntax.lbattrs =
              (uu___356_24616.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___356_24616.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____24623 =
          let uu____24624 =
            let uu____24637 =
              let uu____24644 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____24644)  in
            let uu____24653 = elim_delayed_subst_term t2  in
            (uu____24637, uu____24653)  in
          FStar_Syntax_Syntax.Tm_let uu____24624  in
        mk1 uu____24623
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____24697 =
          let uu____24698 =
            let uu____24705 = elim_delayed_subst_term tm  in
            (uu____24705, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____24698  in
        mk1 uu____24697
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____24716 =
          let uu____24717 =
            let uu____24724 = elim_delayed_subst_term t2  in
            let uu____24727 = elim_delayed_subst_meta md  in
            (uu____24724, uu____24727)  in
          FStar_Syntax_Syntax.Tm_meta uu____24717  in
        mk1 uu____24716

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___269_24736  ->
         match uu___269_24736 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____24740 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____24740
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
        let uu____24763 =
          let uu____24764 =
            let uu____24773 = elim_delayed_subst_term t  in
            (uu____24773, uopt)  in
          FStar_Syntax_Syntax.Total uu____24764  in
        mk1 uu____24763
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____24790 =
          let uu____24791 =
            let uu____24800 = elim_delayed_subst_term t  in
            (uu____24800, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____24791  in
        mk1 uu____24790
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___357_24809 = ct  in
          let uu____24810 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____24813 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____24824 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___357_24809.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___357_24809.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____24810;
            FStar_Syntax_Syntax.effect_args = uu____24813;
            FStar_Syntax_Syntax.flags = uu____24824
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___270_24827  ->
    match uu___270_24827 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____24841 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____24841
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____24880 =
          let uu____24887 = elim_delayed_subst_term t  in (m, uu____24887)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____24880
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____24899 =
          let uu____24908 = elim_delayed_subst_term t  in
          (m1, m2, uu____24908)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____24899
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
      (fun uu____24941  ->
         match uu____24941 with
         | (t,q) ->
             let uu____24960 = elim_delayed_subst_term t  in (uu____24960, q))
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
      (fun uu____24988  ->
         match uu____24988 with
         | (x,q) ->
             let uu____25007 =
               let uu___358_25008 = x  in
               let uu____25009 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___358_25008.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___358_25008.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____25009
               }  in
             (uu____25007, q)) bs

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
            | (uu____25115,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____25147,FStar_Util.Inl t) ->
                let uu____25169 =
                  let uu____25176 =
                    let uu____25177 =
                      let uu____25192 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____25192)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____25177  in
                  FStar_Syntax_Syntax.mk uu____25176  in
                uu____25169 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____25208 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____25208 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____25240 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____25313 ->
                    let uu____25314 =
                      let uu____25323 =
                        let uu____25324 = FStar_Syntax_Subst.compress t4  in
                        uu____25324.FStar_Syntax_Syntax.n  in
                      (uu____25323, tc)  in
                    (match uu____25314 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____25353) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____25400) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____25445,FStar_Util.Inl uu____25446) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____25477 -> failwith "Impossible")
                 in
              (match uu____25240 with
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
          let uu____25614 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____25614 with
          | (univ_names1,binders1,tc) ->
              let uu____25688 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____25688)
  
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
          let uu____25741 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____25741 with
          | (univ_names1,binders1,tc) ->
              let uu____25815 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____25815)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____25856 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____25856 with
           | (univ_names1,binders1,typ1) ->
               let uu___359_25896 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___359_25896.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___359_25896.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___359_25896.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___359_25896.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___360_25911 = s  in
          let uu____25912 =
            let uu____25913 =
              let uu____25922 = FStar_List.map (elim_uvars env) sigs  in
              (uu____25922, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____25913  in
          {
            FStar_Syntax_Syntax.sigel = uu____25912;
            FStar_Syntax_Syntax.sigrng =
              (uu___360_25911.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___360_25911.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___360_25911.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___360_25911.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____25939 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25939 with
           | (univ_names1,uu____25963,typ1) ->
               let uu___361_25985 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___361_25985.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___361_25985.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___361_25985.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___361_25985.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____25991 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25991 with
           | (univ_names1,uu____26015,typ1) ->
               let uu___362_26037 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___362_26037.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___362_26037.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___362_26037.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___362_26037.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____26065 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____26065 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____26090 =
                            let uu____26091 =
                              let uu____26092 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____26092  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____26091
                             in
                          elim_delayed_subst_term uu____26090  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___363_26095 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___363_26095.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___363_26095.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___363_26095.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___363_26095.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___364_26096 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___364_26096.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___364_26096.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___364_26096.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___364_26096.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___365_26102 = s  in
          let uu____26103 =
            let uu____26104 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____26104  in
          {
            FStar_Syntax_Syntax.sigel = uu____26103;
            FStar_Syntax_Syntax.sigrng =
              (uu___365_26102.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___365_26102.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___365_26102.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___365_26102.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____26108 = elim_uvars_aux_t env us [] t  in
          (match uu____26108 with
           | (us1,uu____26132,t1) ->
               let uu___366_26154 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___366_26154.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___366_26154.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___366_26154.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___366_26154.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____26155 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____26157 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____26157 with
           | (univs1,binders,signature) ->
               let uu____26197 =
                 let uu____26202 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____26202 with
                 | (univs_opening,univs2) ->
                     let uu____26225 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____26225)
                  in
               (match uu____26197 with
                | (univs_opening,univs_closing) ->
                    let uu____26228 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____26234 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____26235 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____26234, uu____26235)  in
                    (match uu____26228 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____26261 =
                           match uu____26261 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____26279 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____26279 with
                                | (us1,t1) ->
                                    let uu____26290 =
                                      let uu____26299 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____26310 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____26299, uu____26310)  in
                                    (match uu____26290 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____26339 =
                                           let uu____26348 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____26359 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____26348, uu____26359)  in
                                         (match uu____26339 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____26389 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____26389
                                                 in
                                              let uu____26390 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____26390 with
                                               | (uu____26417,uu____26418,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____26441 =
                                                       let uu____26442 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____26442
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____26441
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____26451 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____26451 with
                           | (uu____26470,uu____26471,t1) -> t1  in
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
                             | uu____26547 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____26574 =
                               let uu____26575 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____26575.FStar_Syntax_Syntax.n  in
                             match uu____26574 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____26634 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____26667 =
                               let uu____26668 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____26668.FStar_Syntax_Syntax.n  in
                             match uu____26667 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____26691) ->
                                 let uu____26716 = destruct_action_body body
                                    in
                                 (match uu____26716 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____26765 ->
                                 let uu____26766 = destruct_action_body t  in
                                 (match uu____26766 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____26821 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____26821 with
                           | (action_univs,t) ->
                               let uu____26830 = destruct_action_typ_templ t
                                  in
                               (match uu____26830 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___367_26877 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___367_26877.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___367_26877.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___368_26879 = ed  in
                           let uu____26880 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____26881 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____26882 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____26883 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____26884 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____26885 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____26886 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____26887 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____26888 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____26889 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____26890 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____26891 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____26892 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____26893 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___368_26879.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___368_26879.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____26880;
                             FStar_Syntax_Syntax.bind_wp = uu____26881;
                             FStar_Syntax_Syntax.if_then_else = uu____26882;
                             FStar_Syntax_Syntax.ite_wp = uu____26883;
                             FStar_Syntax_Syntax.stronger = uu____26884;
                             FStar_Syntax_Syntax.close_wp = uu____26885;
                             FStar_Syntax_Syntax.assert_p = uu____26886;
                             FStar_Syntax_Syntax.assume_p = uu____26887;
                             FStar_Syntax_Syntax.null_wp = uu____26888;
                             FStar_Syntax_Syntax.trivial = uu____26889;
                             FStar_Syntax_Syntax.repr = uu____26890;
                             FStar_Syntax_Syntax.return_repr = uu____26891;
                             FStar_Syntax_Syntax.bind_repr = uu____26892;
                             FStar_Syntax_Syntax.actions = uu____26893;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___368_26879.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___369_26896 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___369_26896.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___369_26896.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___369_26896.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___369_26896.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___271_26917 =
            match uu___271_26917 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____26948 = elim_uvars_aux_t env us [] t  in
                (match uu____26948 with
                 | (us1,uu____26980,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___370_27011 = sub_eff  in
            let uu____27012 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____27015 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___370_27011.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___370_27011.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____27012;
              FStar_Syntax_Syntax.lift = uu____27015
            }  in
          let uu___371_27018 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___371_27018.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___371_27018.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___371_27018.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___371_27018.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____27028 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____27028 with
           | (univ_names1,binders1,comp1) ->
               let uu___372_27068 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___372_27068.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___372_27068.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___372_27068.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___372_27068.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____27071 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____27072 -> s
  
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
        let uu____27119 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____27119 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____27141 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____27141 with
             | (uu____27148,head_def) ->
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
      let uu____27154 = FStar_Syntax_Util.head_and_args t  in
      match uu____27154 with
      | (head1,args) ->
          let uu____27199 =
            let uu____27200 = FStar_Syntax_Subst.compress head1  in
            uu____27200.FStar_Syntax_Syntax.n  in
          (match uu____27199 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____27207;
                  FStar_Syntax_Syntax.vars = uu____27208;_},us)
               -> aux fv us args
           | uu____27214 -> FStar_Pervasives_Native.None)
  