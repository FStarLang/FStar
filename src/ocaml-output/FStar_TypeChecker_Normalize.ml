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
    match projectee with | Clos _0 -> true | uu____127 -> false
  
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
    match projectee with | Univ _0 -> true | uu____231 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____244 -> false
  
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
    match projectee with | Arg _0 -> true | uu____421 -> false
  
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____459 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.universe Prims.list,FStar_Range.range)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____497 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2
      FStar_Syntax_Syntax.memo)
  = fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____570 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env,branches,FStar_TypeChecker_Cfg.cfg,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____620 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,env,FStar_Syntax_Syntax.residual_comp
                                           FStar_Pervasives_Native.option,
      FStar_Range.range) FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____678 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____722 -> false
  
let (__proj__Meta__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.metadata,FStar_Range.range)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____762 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.letbinding,FStar_Range.range)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____800 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> FStar_TypeChecker_Cfg.cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____818 -> false
  
let (__proj__Debug__item___0 :
  stack_elt ->
    (FStar_Syntax_Syntax.term,FStar_Util.time) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____845 = FStar_Syntax_Util.head_and_args' t  in
    match uu____845 with | (hd1,uu____861) -> hd1
  
let mk :
  'Auu____888 .
    'Auu____888 ->
      FStar_Range.range -> 'Auu____888 FStar_Syntax_Syntax.syntax
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
          let uu____951 = FStar_ST.op_Bang r  in
          match uu____951 with
          | FStar_Pervasives_Native.Some uu____999 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____1071 =
      FStar_List.map
        (fun uu____1085  ->
           match uu____1085 with
           | (bopt,c) ->
               let uu____1098 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____1100 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____1098 uu____1100) env
       in
    FStar_All.pipe_right uu____1071 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___252_1103  ->
    match uu___252_1103 with
    | Clos (env,t,uu____1106,uu____1107) ->
        let uu____1152 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____1159 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____1152 uu____1159
    | Univ uu____1160 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___253_1165  ->
    match uu___253_1165 with
    | Arg (c,uu____1167,uu____1168) ->
        let uu____1169 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____1169
    | MemoLazy uu____1170 -> "MemoLazy"
    | Abs (uu____1177,bs,uu____1179,uu____1180,uu____1181) ->
        let uu____1186 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____1186
    | UnivArgs uu____1193 -> "UnivArgs"
    | Match uu____1200 -> "Match"
    | App (uu____1209,t,uu____1211,uu____1212) ->
        let uu____1213 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____1213
    | Meta (uu____1214,m,uu____1216) -> "Meta"
    | Let uu____1217 -> "Let"
    | Cfg uu____1226 -> "Cfg"
    | Debug (t,uu____1228) ->
        let uu____1229 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____1229
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____1239 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____1239 (FStar_String.concat "; ")
  
let is_empty : 'Auu____1248 . 'Auu____1248 Prims.list -> Prims.bool =
  fun uu___254_1255  ->
    match uu___254_1255 with | [] -> true | uu____1258 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        (fun uu___273_1289  ->
           match () with
           | () ->
               let uu____1290 =
                 FStar_List.nth env x.FStar_Syntax_Syntax.index  in
               FStar_Pervasives_Native.snd uu____1290) ()
      with
      | uu___272_1307 ->
          let uu____1308 =
            let uu____1309 = FStar_Syntax_Print.db_to_string x  in
            let uu____1310 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____1309
              uu____1310
             in
          failwith uu____1308
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____1318 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____1318
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____1322 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____1322
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____1326 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____1326
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
          let uu____1360 =
            FStar_List.fold_left
              (fun uu____1386  ->
                 fun u1  ->
                   match uu____1386 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1411 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____1411 with
                        | (k_u,n1) ->
                            let uu____1426 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____1426
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____1360 with
          | (uu____1444,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 (fun uu___275_1469  ->
                    match () with
                    | () ->
                        let uu____1472 =
                          let uu____1473 = FStar_List.nth env x  in
                          FStar_Pervasives_Native.snd uu____1473  in
                        (match uu____1472 with
                         | Univ u3 ->
                             ((let uu____1492 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      cfg.FStar_TypeChecker_Cfg.tcenv)
                                   (FStar_Options.Other "univ_norm")
                                  in
                               if uu____1492
                               then
                                 let uu____1493 =
                                   FStar_Syntax_Print.univ_to_string u3  in
                                 FStar_Util.print1
                                   "Univ (in norm_universe): %s\n" uu____1493
                               else ());
                              aux u3)
                         | Dummy  -> [u2]
                         | uu____1495 ->
                             let uu____1496 =
                               let uu____1497 = FStar_Util.string_of_int x
                                  in
                               FStar_Util.format1
                                 "Impossible: universe variable u@%s bound to a term"
                                 uu____1497
                                in
                             failwith uu____1496)) ()
               with
               | uu____1505 ->
                   if
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else
                     (let uu____1509 =
                        let uu____1510 = FStar_Util.string_of_int x  in
                        Prims.strcat "Universe variable not found: u@"
                          uu____1510
                         in
                      failwith uu____1509))
          | FStar_Syntax_Syntax.U_unif uu____1513 when
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1522 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1531 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1538 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____1538 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____1555 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____1555 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1563 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1571 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____1571 with
                                  | (uu____1576,m) -> n1 <= m))
                           in
                        if uu____1563 then rest1 else us1
                    | uu____1581 -> us1)
               | uu____1586 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1590 = aux u3  in
              FStar_List.map (fun _0_16  -> FStar_Syntax_Syntax.U_succ _0_16)
                uu____1590
           in
        if
          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1594 = aux u  in
           match uu____1594 with
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
            (fun uu____1762  ->
               let uu____1763 = FStar_Syntax_Print.tag_of_term t  in
               let uu____1764 = env_to_string env  in
               let uu____1765 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____1763 uu____1764 uu____1765);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____1774 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____1777 ->
                    let uu____1800 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____1800
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____1801 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____1802 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____1803 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____1804 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____1828 ->
                           let uu____1841 =
                             let uu____1842 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____1843 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____1842 uu____1843
                              in
                           failwith uu____1841
                       | uu____1846 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___255_1881  ->
                                         match uu___255_1881 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____1888 =
                                               let uu____1895 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____1895)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____1888
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___276_1905 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___276_1905.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___276_1905.FStar_Syntax_Syntax.sort)
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
                                              | uu____1910 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____1913 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___277_1917 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___277_1917.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___277_1917.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____1938 =
                        let uu____1939 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____1939  in
                      mk uu____1938 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____1947 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1947  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____1949 = lookup_bvar env x  in
                    (match uu____1949 with
                     | Univ uu____1952 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___278_1956 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___278_1956.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___278_1956.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____1962,uu____1963) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____2052  ->
                              fun stack1  ->
                                match uu____2052 with
                                | (a,aq) ->
                                    let uu____2064 =
                                      let uu____2065 =
                                        let uu____2072 =
                                          let uu____2073 =
                                            let uu____2104 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____2104, false)  in
                                          Clos uu____2073  in
                                        (uu____2072, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____2065  in
                                    uu____2064 :: stack1) args)
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
                    let uu____2292 = close_binders cfg env bs  in
                    (match uu____2292 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____2347 =
                      let uu____2360 =
                        let uu____2369 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____2369]  in
                      close_binders cfg env uu____2360  in
                    (match uu____2347 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____2414 =
                             let uu____2415 =
                               let uu____2422 =
                                 let uu____2423 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____2423
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____2422, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____2415  in
                           mk uu____2414 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____2522 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____2522
                      | FStar_Util.Inr c ->
                          let uu____2536 = close_comp cfg env c  in
                          FStar_Util.Inr uu____2536
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____2555 =
                        let uu____2556 =
                          let uu____2583 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____2583, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____2556  in
                      mk uu____2555 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____2629 =
                            let uu____2630 =
                              let uu____2637 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____2637, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____2630  in
                          mk uu____2629 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____2689  -> dummy :: env1) env
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
                    let uu____2710 =
                      let uu____2721 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____2721
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____2740 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___279_2756 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___279_2756.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___279_2756.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____2740))
                       in
                    (match uu____2710 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___280_2774 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___280_2774.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___280_2774.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___280_2774.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___280_2774.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____2788,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____2851  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____2868 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____2868
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____2880  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____2904 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____2904
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___281_2912 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___281_2912.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___281_2912.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___282_2913 = lb  in
                      let uu____2914 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___282_2913.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___282_2913.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____2914;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___282_2913.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___282_2913.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____2946  -> fun env1  -> dummy :: env1)
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
            (fun uu____3035  ->
               let uu____3036 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3037 = env_to_string env  in
               let uu____3038 = stack_to_string stack  in
               let uu____3039 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____3036 uu____3037 uu____3038 uu____3039);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____3044,uu____3045),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____3124 = close_binders cfg env' bs  in
               (match uu____3124 with
                | (bs1,uu____3140) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____3160 =
                      let uu___283_3163 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___283_3163.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___283_3163.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____3160)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____3219 =
                 match uu____3219 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____3334 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____3363 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____3447  ->
                                     fun uu____3448  ->
                                       match (uu____3447, uu____3448) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____3587 = norm_pat env4 p1
                                              in
                                           (match uu____3587 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____3363 with
                            | (pats1,env4) ->
                                ((let uu___284_3749 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___284_3749.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___285_3768 = x  in
                             let uu____3769 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___285_3768.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___285_3768.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3769
                             }  in
                           ((let uu___286_3783 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___286_3783.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___287_3794 = x  in
                             let uu____3795 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___287_3794.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___287_3794.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3795
                             }  in
                           ((let uu___288_3809 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___288_3809.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___289_3825 = x  in
                             let uu____3826 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___289_3825.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___289_3825.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3826
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___290_3843 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___290_3843.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____3848 = norm_pat env2 pat  in
                     (match uu____3848 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____3917 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____3917
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____3936 =
                   let uu____3937 =
                     let uu____3960 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____3960)  in
                   FStar_Syntax_Syntax.Tm_match uu____3937  in
                 mk uu____3936 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____4075 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____4184  ->
                                       match uu____4184 with
                                       | (a,q) ->
                                           let uu____4211 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____4211, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____4075
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____4224 =
                       let uu____4231 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____4231)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____4224
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____4243 =
                       let uu____4252 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____4252)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____4243
                 | uu____4257 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____4263 -> failwith "Impossible: unexpected stack element")

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
            let uu____4278 =
              let uu____4279 = inline_closure_env cfg env [] t  in
              FStar_Syntax_Syntax.Meta uu____4279  in
            FStar_Pervasives_Native.Some uu____4278
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
        let uu____4296 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4380  ->
                  fun uu____4381  ->
                    match (uu____4380, uu____4381) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___291_4521 = b  in
                          let uu____4522 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___291_4521.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___291_4521.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4522
                          }  in
                        let imp1 = close_imp cfg env1 imp  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp1) :: out))) (env, []))
           in
        match uu____4296 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____4662 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4675 = inline_closure_env cfg env [] t  in
                 let uu____4676 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____4675 uu____4676
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4689 = inline_closure_env cfg env [] t  in
                 let uu____4690 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4689 uu____4690
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____4744  ->
                           match uu____4744 with
                           | (a,q) ->
                               let uu____4765 =
                                 inline_closure_env cfg env [] a  in
                               (uu____4765, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___256_4782  ->
                           match uu___256_4782 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4786 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____4786
                           | f -> f))
                    in
                 let uu____4790 =
                   let uu___292_4791 = c1  in
                   let uu____4792 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4792;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___292_4791.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____4790)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___257_4802  ->
            match uu___257_4802 with
            | FStar_Syntax_Syntax.DECREASES uu____4803 -> false
            | uu____4806 -> true))

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
                   (fun uu___258_4824  ->
                      match uu___258_4824 with
                      | FStar_Syntax_Syntax.DECREASES uu____4825 -> false
                      | uu____4828 -> true))
               in
            let rc1 =
              let uu___293_4830 = rc  in
              let uu____4831 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___293_4830.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4831;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____4840 -> lopt

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
    let uu____4907 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____4907 with
    | FStar_Pervasives_Native.Some e ->
        let uu____4946 = FStar_Syntax_Embeddings.unembed e t  in
        uu____4946 true FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____4966 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____4966) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____5028  ->
           fun subst1  ->
             match uu____5028 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____5069,uu____5070)) ->
                      let uu____5129 = b  in
                      (match uu____5129 with
                       | (bv,uu____5137) ->
                           let uu____5138 =
                             let uu____5139 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____5139  in
                           if uu____5138
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____5144 = unembed_binder term1  in
                              match uu____5144 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____5151 =
                                      let uu___294_5152 = bv  in
                                      let uu____5153 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___294_5152.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___294_5152.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____5153
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____5151
                                     in
                                  let b_for_x =
                                    let uu____5159 =
                                      let uu____5166 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____5166)
                                       in
                                    FStar_Syntax_Syntax.NT uu____5159  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___259_5182  ->
                                         match uu___259_5182 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____5183,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____5185;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____5186;_})
                                             ->
                                             let uu____5191 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____5191
                                         | uu____5192 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____5193 -> subst1)) env []
  
let reduce_primops :
  'Auu____5215 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv,'Auu____5215) FStar_Pervasives_Native.tuple2
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
            (let uu____5267 = FStar_Syntax_Util.head_and_args tm  in
             match uu____5267 with
             | (head1,args) ->
                 let uu____5312 =
                   let uu____5313 = FStar_Syntax_Util.un_uinst head1  in
                   uu____5313.FStar_Syntax_Syntax.n  in
                 (match uu____5312 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____5319 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                      (match uu____5319 with
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
                                (fun uu____5347  ->
                                   let uu____5348 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name
                                      in
                                   let uu____5349 =
                                     FStar_Util.string_of_int l  in
                                   let uu____5356 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____5348 uu____5349 uu____5356);
                              tm)
                           else
                             (let uu____5358 =
                                if l = prim_step.FStar_TypeChecker_Cfg.arity
                                then (args, [])
                                else
                                  FStar_List.splitAt
                                    prim_step.FStar_TypeChecker_Cfg.arity
                                    args
                                 in
                              match uu____5358 with
                              | (args_1,args_2) ->
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____5445  ->
                                        let uu____5446 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____5446);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____5449  ->
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
                                           (fun uu____5463  ->
                                              let uu____5464 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____5464);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5470  ->
                                              let uu____5471 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____5472 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____5471 uu____5472);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____5473 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____5477  ->
                                 let uu____5478 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____5478);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5482  ->
                            let uu____5483 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5483);
                       (match args with
                        | (a1,uu____5487)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____5512 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5526  ->
                            let uu____5527 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5527);
                       (match args with
                        | (t,uu____5531)::(r,uu____5533)::[] ->
                            let uu____5574 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____5574 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____5580 -> tm))
                  | uu____5591 -> tm))
  
let reduce_equality :
  'Auu____5602 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv,'Auu____5602) FStar_Pervasives_Native.tuple2
           FStar_Pervasives_Native.option,closure)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun tm  ->
        reduce_primops norm_cb
          (let uu___295_5655 = cfg  in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___296_5658 = FStar_TypeChecker_Cfg.default_steps  in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___296_5658.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___296_5658.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___296_5658.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___296_5658.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___296_5658.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___296_5658.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___296_5658.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___296_5658.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___296_5658.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___296_5658.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___296_5658.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___296_5658.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___296_5658.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___296_5658.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___296_5658.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___296_5658.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___296_5658.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___296_5658.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___296_5658.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___296_5658.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___296_5658.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___296_5658.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___296_5658.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___296_5658.FStar_TypeChecker_Cfg.nbe_step)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___295_5655.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___295_5655.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___295_5655.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___295_5655.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___295_5655.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___295_5655.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___295_5655.FStar_TypeChecker_Cfg.reifying)
           }) tm
  
let is_norm_request :
  'Auu____5665 .
    FStar_Syntax_Syntax.term -> 'Auu____5665 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____5680 =
        let uu____5687 =
          let uu____5688 = FStar_Syntax_Util.un_uinst hd1  in
          uu____5688.FStar_Syntax_Syntax.n  in
        (uu____5687, args)  in
      match uu____5680 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5694::uu____5695::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5699::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____5704::uu____5705::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____5708 -> false
  
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s  ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
  
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___260_5730  ->
    match uu___260_5730 with
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
        let uu____5736 =
          let uu____5739 =
            let uu____5740 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldOnly uu____5740  in
          [uu____5739]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____5736
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____5746 =
          let uu____5749 =
            let uu____5750 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldFully uu____5750  in
          [uu____5749]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____5746
    | FStar_Syntax_Embeddings.UnfoldAttr names1 ->
        let uu____5756 =
          let uu____5759 =
            let uu____5760 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldAttr uu____5760  in
          [uu____5759]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____5756
    | FStar_Syntax_Embeddings.NBE  -> [FStar_TypeChecker_Env.NBE]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  = fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____5782 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term,'Auu____5782)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____5833 =
            let uu____5838 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____5838 s  in
          match uu____5833 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____5854 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____5854
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
        | uu____5880::(tm,uu____5882)::[] ->
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
        | (tm,uu____5911)::[] ->
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
        | (steps,uu____5932)::uu____5933::(tm,uu____5935)::[] ->
            let add_exclude s z =
              let uu____5973 =
                FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s  in
              if uu____5973
              then s
              else (FStar_TypeChecker_Env.Exclude z) :: s  in
            let uu____5977 =
              let uu____5982 = full_norm steps  in parse_steps uu____5982  in
            (match uu____5977 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = FStar_TypeChecker_Env.Beta :: s  in
                 let s2 = add_exclude s1 FStar_TypeChecker_Env.Zeta  in
                 let s3 = add_exclude s2 FStar_TypeChecker_Env.Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____6021 -> FStar_Pervasives_Native.None
  
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun s  ->
      fun tm  ->
        let delta_level =
          let uu____6052 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___261_6057  ->
                    match uu___261_6057 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____6058 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____6059 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____6062 -> true
                    | uu____6065 -> false))
             in
          if uu____6052
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta]  in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____6072  ->
             let uu____6073 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____6073);
        (let tm_norm =
           let uu____6075 =
             let uu____6090 = FStar_TypeChecker_Cfg.cfg_env cfg  in
             uu____6090.FStar_TypeChecker_Env.nbe  in
           uu____6075 s cfg.FStar_TypeChecker_Cfg.tcenv tm  in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____6094  ->
              let uu____6095 = FStar_Syntax_Print.term_to_string tm_norm  in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____6095);
         tm_norm)
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___262_6102  ->
    match uu___262_6102 with
    | (App
        (uu____6105,{
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reify );
                      FStar_Syntax_Syntax.pos = uu____6106;
                      FStar_Syntax_Syntax.vars = uu____6107;_},uu____6108,uu____6109))::uu____6110
        -> true
    | uu____6115 -> false
  
let firstn :
  'Auu____6124 .
    Prims.int ->
      'Auu____6124 Prims.list ->
        ('Auu____6124 Prims.list,'Auu____6124 Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack  ->
      let rec drop_irrel uu___263_6175 =
        match uu___263_6175 with
        | (MemoLazy uu____6180)::s -> drop_irrel s
        | s -> s  in
      let uu____6193 = drop_irrel stack  in
      match uu____6193 with
      | (App
          (uu____6196,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____6197;
                        FStar_Syntax_Syntax.vars = uu____6198;_},uu____6199,uu____6200))::uu____6201
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____6206 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____6229) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____6239) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____6260  ->
                  match uu____6260 with
                  | (a,uu____6270) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6280 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____6303 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____6304 -> false
    | FStar_Syntax_Syntax.Tm_type uu____6317 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____6318 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____6319 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____6320 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____6321 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____6322 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____6329 -> false
    | FStar_Syntax_Syntax.Tm_let uu____6336 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____6349 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____6368 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____6383 -> true
    | FStar_Syntax_Syntax.Tm_match uu____6390 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____6460  ->
                   match uu____6460 with
                   | (a,uu____6470) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____6481) ->
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
                     (fun uu____6609  ->
                        match uu____6609 with
                        | (a,uu____6619) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____6628,uu____6629,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____6635,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____6641 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____6648 -> false
            | FStar_Syntax_Syntax.Meta_named uu____6649 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____6655 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____6661 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_fully  -> true | uu____6667 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_reify  -> true | uu____6673 -> false
  
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
            let uu____6702 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
            match uu____6702 with
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
              (fun uu____6830  ->
                 fun uu____6831  ->
                   match (uu____6830, uu____6831) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____6891 =
            match uu____6891 with
            | (x,y,z) ->
                let uu____6901 = FStar_Util.string_of_bool x  in
                let uu____6902 = FStar_Util.string_of_bool y  in
                let uu____6903 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____6901 uu____6902
                  uu____6903
             in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg  in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____6922  ->
                    let uu____6923 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____6924 = FStar_Util.string_of_bool b  in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____6923 uu____6924);
               if b then reif else no)
            else
              if
                (let uu____6932 = FStar_TypeChecker_Cfg.find_prim_step cfg fv
                    in
                 FStar_Option.isSome uu____6932)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____6937  ->
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
                          ((is_rec,uu____6971),uu____6972);
                        FStar_Syntax_Syntax.sigrng = uu____6973;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____6975;
                        FStar_Syntax_Syntax.sigattrs = uu____6976;_},uu____6977),uu____6978),uu____6979,uu____6980,uu____6981)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7086  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____7087,uu____7088,uu____7089,uu____7090) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7157  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____7159),uu____7160);
                        FStar_Syntax_Syntax.sigrng = uu____7161;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7163;
                        FStar_Syntax_Syntax.sigattrs = uu____7164;_},uu____7165),uu____7166),uu____7167,uu____7168,uu____7169)
                     when
                     is_rec &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7274  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____7275,FStar_Pervasives_Native.Some
                    uu____7276,uu____7277,uu____7278) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7346  ->
                           let uu____7347 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____7347);
                      (let uu____7348 =
                         let uu____7357 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____7377 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____7377
                            in
                         let uu____7384 =
                           let uu____7393 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____7413 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____7413
                              in
                           let uu____7424 =
                             let uu____7433 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____7453 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____7453
                                in
                             [uu____7433]  in
                           uu____7393 :: uu____7424  in
                         uu____7357 :: uu____7384  in
                       comb_or uu____7348))
                 | (uu____7484,uu____7485,FStar_Pervasives_Native.Some
                    uu____7486,uu____7487) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7555  ->
                           let uu____7556 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____7556);
                      (let uu____7557 =
                         let uu____7566 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____7586 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____7586
                            in
                         let uu____7593 =
                           let uu____7602 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____7622 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____7622
                              in
                           let uu____7633 =
                             let uu____7642 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____7662 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____7662
                                in
                             [uu____7642]  in
                           uu____7602 :: uu____7633  in
                         uu____7566 :: uu____7593  in
                       comb_or uu____7557))
                 | (uu____7693,uu____7694,uu____7695,FStar_Pervasives_Native.Some
                    uu____7696) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7764  ->
                           let uu____7765 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____7765);
                      (let uu____7766 =
                         let uu____7775 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____7795 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____7795
                            in
                         let uu____7802 =
                           let uu____7811 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____7831 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____7831
                              in
                           let uu____7842 =
                             let uu____7851 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____7871 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____7871
                                in
                             [uu____7851]  in
                           uu____7811 :: uu____7842  in
                         uu____7775 :: uu____7802  in
                       comb_or uu____7766))
                 | uu____7902 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7948  ->
                           let uu____7949 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____7950 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____7951 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level
                              in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____7949 uu____7950 uu____7951);
                      (let uu____7952 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___264_7956  ->
                                 match uu___264_7956 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.InliningDelta  ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____7958 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv
                                        in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____7958 l))
                          in
                       FStar_All.pipe_left yesno uu____7952)))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____7970  ->
               let uu____7971 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____7972 =
                 let uu____7973 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____7973  in
               let uu____7974 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____7971 uu____7972 uu____7974);
          (match res with
           | (false ,uu____7975,uu____7976) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____7977 ->
               let uu____7984 =
                 let uu____7985 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____7985
                  in
               FStar_All.pipe_left failwith uu____7984)
  
let decide_unfolding :
  'Auu____8000 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'Auu____8000 ->
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
                    let uu___297_8069 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___298_8072 = cfg.FStar_TypeChecker_Cfg.steps
                            in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___298_8072.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___298_8072.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___298_8072.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___298_8072.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___298_8072.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___298_8072.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___298_8072.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___298_8072.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___298_8072.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___298_8072.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___298_8072.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___298_8072.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___298_8072.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___298_8072.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___298_8072.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___298_8072.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___298_8072.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___298_8072.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___298_8072.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___298_8072.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___298_8072.FStar_TypeChecker_Cfg.nbe_step)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___297_8069.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___297_8069.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___297_8069.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___297_8069.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___297_8069.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___297_8069.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___297_8069.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___297_8069.FStar_TypeChecker_Cfg.reifying)
                    }  in
                  let stack' =
                    match stack with
                    | (UnivArgs (us,r))::stack' -> (UnivArgs (us, r)) ::
                        (Cfg cfg) :: stack'
                    | stack' -> (Cfg cfg) :: stack'  in
                  FStar_Pervasives_Native.Some (cfg', stack')
              | Should_unfold_reify  ->
                  let ref =
                    let uu____8109 =
                      let uu____8116 =
                        let uu____8117 =
                          let uu____8118 = FStar_Syntax_Syntax.lid_of_fv fv
                             in
                          FStar_Const.Const_reflect uu____8118  in
                        FStar_Syntax_Syntax.Tm_constant uu____8117  in
                      FStar_Syntax_Syntax.mk uu____8116  in
                    uu____8109 FStar_Pervasives_Native.None
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
               | FStar_Syntax_Syntax.Tm_delayed uu____8406 ->
                   let uu____8429 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____8429
               | uu____8430 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____8439  ->
               let uu____8440 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____8441 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____8442 = FStar_Syntax_Print.term_to_string t1  in
               let uu____8443 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____8450 =
                 let uu____8451 =
                   let uu____8454 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8454
                    in
                 stack_to_string uu____8451  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____8440 uu____8441 uu____8442 uu____8443 uu____8450);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____8480  ->
               let uu____8481 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____8481);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8485  ->
                     let uu____8486 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8486);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____8487 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8491  ->
                     let uu____8492 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8492);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____8493 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8497  ->
                     let uu____8498 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8498);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____8499 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8503  ->
                     let uu____8504 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8504);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8505;
                 FStar_Syntax_Syntax.fv_delta = uu____8506;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8510  ->
                     let uu____8511 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8511);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8512;
                 FStar_Syntax_Syntax.fv_delta = uu____8513;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____8514);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8524  ->
                     let uu____8525 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8525);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid
                  in
               let uu____8529 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
               (match uu____8529 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level _0_17) when
                    _0_17 = (Prims.parse_int "0") ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____8535  ->
                          let uu____8536 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____8536);
                     rebuild cfg env stack t1)
                | uu____8537 ->
                    let uu____8540 =
                      decide_unfolding cfg env stack
                        t1.FStar_Syntax_Syntax.pos fv qninfo
                       in
                    (match uu____8540 with
                     | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                         do_unfold_fv cfg1 env stack1 t1 qninfo fv
                     | FStar_Pervasives_Native.None  ->
                         rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_quoted uu____8567 ->
               let uu____8574 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____8574
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
                  && (is_norm_request hd1 args))
                 &&
                 (let uu____8610 =
                    FStar_Ident.lid_equals
                      (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____8610)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___299_8614 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___300_8617 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___300_8617.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___300_8617.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___300_8617.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___300_8617.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___300_8617.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___300_8617.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___300_8617.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___300_8617.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___300_8617.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___300_8617.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___300_8617.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___300_8617.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___300_8617.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___300_8617.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___300_8617.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___300_8617.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___300_8617.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___300_8617.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___300_8617.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___300_8617.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___300_8617.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___300_8617.FStar_TypeChecker_Cfg.nbe_step)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___299_8614.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___299_8614.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___299_8614.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___299_8614.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___299_8614.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___299_8614.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____8622 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____8622 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____8655  ->
                                 fun stack1  ->
                                   match uu____8655 with
                                   | (a,aq) ->
                                       let uu____8667 =
                                         let uu____8668 =
                                           let uu____8675 =
                                             let uu____8676 =
                                               let uu____8707 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____8707, false)
                                                in
                                             Clos uu____8676  in
                                           (uu____8675, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____8668  in
                                       uu____8667 :: stack1) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____8795  ->
                            let uu____8796 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____8796);
                       norm cfg env stack1 hd1))
                 | FStar_Pervasives_Native.Some (s,tm) when is_nbe_request s
                     ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____8818 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting NBE request on %s ... \n" uu____8818)
                      else ();
                      (let tm' = closure_as_term cfg env tm  in
                       let start = FStar_Util.now ()  in
                       let tm_norm = nbe_eval cfg s tm'  in
                       let fin = FStar_Util.now ()  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         (let uu____8825 =
                            let uu____8826 =
                              let uu____8827 = FStar_Util.time_diff start fin
                                 in
                              FStar_Pervasives_Native.snd uu____8827  in
                            FStar_Util.string_of_int uu____8826  in
                          let uu____8832 =
                            FStar_Syntax_Print.term_to_string tm'  in
                          let uu____8833 =
                            FStar_Syntax_Print.term_to_string tm_norm  in
                          FStar_Util.print3 "NBE'd (%s ms) %s\n\tto %s\n"
                            uu____8825 uu____8832 uu____8833)
                       else ();
                       norm cfg env stack tm_norm))
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____8848 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting norm request on %s ... \n" uu____8848)
                      else ();
                      (let delta_level =
                         let uu____8853 =
                           FStar_All.pipe_right s
                             (FStar_Util.for_some
                                (fun uu___265_8858  ->
                                   match uu___265_8858 with
                                   | FStar_TypeChecker_Env.UnfoldUntil
                                       uu____8859 -> true
                                   | FStar_TypeChecker_Env.UnfoldOnly
                                       uu____8860 -> true
                                   | FStar_TypeChecker_Env.UnfoldFully
                                       uu____8863 -> true
                                   | uu____8866 -> false))
                            in
                         if uu____8853
                         then
                           [FStar_TypeChecker_Env.Unfold
                              FStar_Syntax_Syntax.delta_constant]
                         else [FStar_TypeChecker_Env.NoDelta]  in
                       let cfg'1 =
                         let uu___301_8871 = cfg  in
                         let uu____8872 =
                           let uu___302_8873 =
                             FStar_TypeChecker_Cfg.to_fsteps s  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___302_8873.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___302_8873.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___302_8873.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak =
                               (uu___302_8873.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___302_8873.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___302_8873.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___302_8873.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___302_8873.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               (uu___302_8873.FStar_TypeChecker_Cfg.unfold_only);
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___302_8873.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___302_8873.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___302_8873.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___302_8873.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___302_8873.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___302_8873.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___302_8873.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___302_8873.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___302_8873.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___302_8873.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___302_8873.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___302_8873.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___302_8873.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               true;
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___302_8873.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___302_8873.FStar_TypeChecker_Cfg.nbe_step)
                           }  in
                         {
                           FStar_TypeChecker_Cfg.steps = uu____8872;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___301_8871.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___301_8871.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = delta_level;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___301_8871.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong =
                             (uu___301_8871.FStar_TypeChecker_Cfg.strong);
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___301_8871.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___301_8871.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let stack' =
                         let tail1 = (Cfg cfg) :: stack  in
                         if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           let uu____8878 =
                             let uu____8879 =
                               let uu____8884 = FStar_Util.now ()  in
                               (t1, uu____8884)  in
                             Debug uu____8879  in
                           uu____8878 :: tail1
                         else tail1  in
                       norm cfg'1 env stack' tm))))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____8888 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____8888
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____8897 =
                      let uu____8904 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____8904, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____8897  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____8913 = lookup_bvar env x  in
               (match uu____8913 with
                | Univ uu____8914 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                    then
                      let uu____8963 = FStar_ST.op_Bang r  in
                      (match uu____8963 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9081  ->
                                 let uu____9082 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____9083 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____9082
                                   uu____9083);
                            (let uu____9084 = maybe_weakly_reduced t'  in
                             if uu____9084
                             then
                               match stack with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____9085 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____9160)::uu____9161 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____9171,uu____9172))::stack_rest ->
                    (match c with
                     | Univ uu____9176 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____9185 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____9214  ->
                                    let uu____9215 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____9215);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____9249  ->
                                    let uu____9250 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____9250);
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
                       (fun uu____9318  ->
                          let uu____9319 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____9319);
                     norm cfg env stack1 t1)
                | (Match uu____9320)::uu____9321 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9334 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9334 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9370  -> dummy :: env1) env)
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
                                          let uu____9413 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9413)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___303_9420 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___303_9420.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___303_9420.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9421 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9427  ->
                                 let uu____9428 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9428);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___304_9439 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___304_9439.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___304_9439.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___304_9439.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___304_9439.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___304_9439.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___304_9439.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___304_9439.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___304_9439.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____9442)::uu____9443 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9452 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9452 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9488  -> dummy :: env1) env)
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
                                          let uu____9531 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9531)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___303_9538 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___303_9538.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___303_9538.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9539 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9545  ->
                                 let uu____9546 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9546);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___304_9557 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___304_9557.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___304_9557.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___304_9557.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___304_9557.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___304_9557.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___304_9557.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___304_9557.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___304_9557.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____9560)::uu____9561 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9572 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9572 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9608  -> dummy :: env1) env)
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
                                          let uu____9651 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9651)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___303_9658 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___303_9658.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___303_9658.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9659 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9665  ->
                                 let uu____9666 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9666);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___304_9677 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___304_9677.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___304_9677.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___304_9677.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___304_9677.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___304_9677.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___304_9677.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___304_9677.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___304_9677.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____9680)::uu____9681 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9694 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9694 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9730  -> dummy :: env1) env)
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
                                          let uu____9773 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9773)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___303_9780 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___303_9780.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___303_9780.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9781 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9787  ->
                                 let uu____9788 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9788);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___304_9799 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___304_9799.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___304_9799.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___304_9799.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___304_9799.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___304_9799.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___304_9799.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___304_9799.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___304_9799.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____9802)::uu____9803 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9816 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9816 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9852  -> dummy :: env1) env)
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
                                          let uu____9895 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9895)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___303_9902 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___303_9902.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___303_9902.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9903 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9909  ->
                                 let uu____9910 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9910);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___304_9921 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___304_9921.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___304_9921.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___304_9921.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___304_9921.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___304_9921.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___304_9921.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___304_9921.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___304_9921.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____9924)::uu____9925 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____9942 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9942 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9978  -> dummy :: env1) env)
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
                                          let uu____10021 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10021)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___303_10028 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___303_10028.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___303_10028.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10029 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10035  ->
                                 let uu____10036 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10036);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___304_10047 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___304_10047.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___304_10047.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___304_10047.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___304_10047.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___304_10047.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___304_10047.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___304_10047.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___304_10047.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____10052 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10052 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10088  -> dummy :: env1) env)
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
                                          let uu____10131 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10131)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___303_10138 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___303_10138.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___303_10138.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10139 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10145  ->
                                 let uu____10146 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10146);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___304_10157 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___304_10157.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___304_10157.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___304_10157.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___304_10157.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___304_10157.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___304_10157.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___304_10157.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___304_10157.FStar_TypeChecker_Cfg.reifying)
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
                      (fun uu____10200  ->
                         fun stack1  ->
                           match uu____10200 with
                           | (a,aq) ->
                               let uu____10212 =
                                 let uu____10213 =
                                   let uu____10220 =
                                     let uu____10221 =
                                       let uu____10252 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____10252, false)  in
                                     Clos uu____10221  in
                                   (uu____10220, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____10213  in
                               uu____10212 :: stack1) args)
                  in
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____10340  ->
                     let uu____10341 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____10341);
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
                             ((let uu___305_10389 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___305_10389.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___305_10389.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____10390 ->
                      let uu____10405 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10405)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____10408 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____10408 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____10439 =
                          let uu____10440 =
                            let uu____10447 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___306_10453 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___306_10453.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___306_10453.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____10447)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____10440  in
                        mk uu____10439 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____10476 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____10476
               else
                 (let uu____10478 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____10478 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____10486 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____10512  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____10486 c1  in
                      let t2 =
                        let uu____10536 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____10536 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____10649)::uu____10650 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10663  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____10664)::uu____10665 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10676  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____10677,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____10678;
                                   FStar_Syntax_Syntax.vars = uu____10679;_},uu____10680,uu____10681))::uu____10682
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10689  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____10690)::uu____10691 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10702  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____10703 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10706  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____10710  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____10735 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____10735
                         | FStar_Util.Inr c ->
                             let uu____10749 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____10749
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____10772 =
                               let uu____10773 =
                                 let uu____10800 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____10800, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____10773
                                in
                             mk uu____10772 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____10835 ->
                           let uu____10836 =
                             let uu____10837 =
                               let uu____10838 =
                                 let uu____10865 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____10865, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____10838
                                in
                             mk uu____10837 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____10836))))
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
                   let uu___307_10942 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___308_10945 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___308_10945.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___308_10945.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___308_10945.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___308_10945.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___308_10945.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___308_10945.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___308_10945.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___308_10945.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___308_10945.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___308_10945.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___308_10945.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___308_10945.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___308_10945.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___308_10945.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___308_10945.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___308_10945.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___308_10945.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___308_10945.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___308_10945.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___308_10945.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___308_10945.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___308_10945.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___308_10945.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___308_10945.FStar_TypeChecker_Cfg.nbe_step)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___307_10942.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___307_10942.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___307_10942.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___307_10942.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___307_10942.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___307_10942.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___307_10942.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___307_10942.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____10981 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____10981 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___309_11001 = cfg  in
                               let uu____11002 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___309_11001.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____11002;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___309_11001.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___309_11001.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___309_11001.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___309_11001.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___309_11001.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___309_11001.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___309_11001.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____11009 =
                                 let uu____11010 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____11010  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____11009
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___310_11013 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___310_11013.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___310_11013.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___310_11013.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___310_11013.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____11014 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____11014
           | FStar_Syntax_Syntax.Tm_let
               ((uu____11025,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____11026;
                               FStar_Syntax_Syntax.lbunivs = uu____11027;
                               FStar_Syntax_Syntax.lbtyp = uu____11028;
                               FStar_Syntax_Syntax.lbeff = uu____11029;
                               FStar_Syntax_Syntax.lbdef = uu____11030;
                               FStar_Syntax_Syntax.lbattrs = uu____11031;
                               FStar_Syntax_Syntax.lbpos = uu____11032;_}::uu____11033),uu____11034)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name
                   cfg.FStar_TypeChecker_Cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____11074 =
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
               if uu____11074
               then
                 let binder =
                   let uu____11076 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____11076  in
                 let env1 =
                   let uu____11086 =
                     let uu____11093 =
                       let uu____11094 =
                         let uu____11125 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____11125,
                           false)
                          in
                       Clos uu____11094  in
                     ((FStar_Pervasives_Native.Some binder), uu____11093)  in
                   uu____11086 :: env  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____11220  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                 then
                   (FStar_TypeChecker_Cfg.log cfg
                      (fun uu____11224  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____11225 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____11225))
                 else
                   (let uu____11227 =
                      let uu____11232 =
                        let uu____11233 =
                          let uu____11240 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____11240
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____11233]  in
                      FStar_Syntax_Subst.open_term uu____11232 body  in
                    match uu____11227 with
                    | (bs,body1) ->
                        (FStar_TypeChecker_Cfg.log cfg
                           (fun uu____11267  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____11275 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____11275  in
                            FStar_Util.Inl
                              (let uu___311_11291 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___311_11291.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___311_11291.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____11294  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___312_11296 = lb  in
                             let uu____11297 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___312_11296.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___312_11296.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____11297;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___312_11296.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___312_11296.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11326  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___313_11351 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps =
                                 (uu___313_11351.FStar_TypeChecker_Cfg.steps);
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___313_11351.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___313_11351.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 (uu___313_11351.FStar_TypeChecker_Cfg.delta_level);
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___313_11351.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong = true;
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___313_11351.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___313_11351.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___313_11351.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           FStar_TypeChecker_Cfg.log cfg1
                             (fun uu____11354  ->
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
               let uu____11371 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____11371 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____11407 =
                               let uu___314_11408 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___314_11408.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___314_11408.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____11407  in
                           let uu____11409 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____11409 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____11435 =
                                   FStar_List.map (fun uu____11451  -> dummy)
                                     lbs1
                                    in
                                 let uu____11452 =
                                   let uu____11461 =
                                     FStar_List.map
                                       (fun uu____11483  -> dummy) xs1
                                      in
                                   FStar_List.append uu____11461 env  in
                                 FStar_List.append uu____11435 uu____11452
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____11509 =
                                       let uu___315_11510 = rc  in
                                       let uu____11511 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___315_11510.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____11511;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___315_11510.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____11509
                                 | uu____11520 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___316_11526 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___316_11526.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___316_11526.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___316_11526.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___316_11526.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____11536 =
                        FStar_List.map (fun uu____11552  -> dummy) lbs2  in
                      FStar_List.append uu____11536 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____11560 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____11560 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___317_11576 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___317_11576.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___317_11576.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
               ->
               let uu____11605 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____11605
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____11624 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____11700  ->
                        match uu____11700 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___318_11821 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___318_11821.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___318_11821.FStar_Syntax_Syntax.sort)
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
               (match uu____11624 with
                | (rec_env,memos,uu____12048) ->
                    let uu____12101 =
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
                             let uu____12412 =
                               let uu____12419 =
                                 let uu____12420 =
                                   let uu____12451 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____12451, false)
                                    in
                                 Clos uu____12420  in
                               (FStar_Pervasives_Native.None, uu____12419)
                                in
                             uu____12412 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____12555  ->
                     let uu____12556 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____12556);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____12578 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____12580::uu____12581 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____12586) ->
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
                             | uu____12613 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____12629 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____12629
                              | uu____12642 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____12648 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____12672 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____12686 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____12699 =
                        let uu____12700 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____12701 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____12700 uu____12701
                         in
                      failwith uu____12699
                    else
                      (let uu____12703 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____12703)
                | uu____12704 -> norm cfg env stack t2))

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
              let uu____12713 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____12713 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____12727  ->
                        let uu____12728 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____12728);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____12739  ->
                        let uu____12740 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____12741 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____12740 uu____12741);
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
                      | (UnivArgs (us',uu____12754))::stack1 ->
                          ((let uu____12763 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____12763
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____12767 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____12767) us'
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
                      | uu____12800 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____12803 ->
                          let uu____12806 =
                            let uu____12807 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____12807
                             in
                          failwith uu____12806
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
                  let uu___319_12831 = cfg  in
                  let uu____12832 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____12832;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___319_12831.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___319_12831.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___319_12831.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___319_12831.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___319_12831.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___319_12831.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___319_12831.FStar_TypeChecker_Cfg.reifying)
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
                     (uu____12862,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____12863;
                                    FStar_Syntax_Syntax.vars = uu____12864;_},uu____12865,uu____12866))::uu____12867
                     -> ()
                 | uu____12872 ->
                     let uu____12875 =
                       let uu____12876 = stack_to_string stack  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____12876
                        in
                     failwith uu____12875);
                (let head0 = head1  in
                 let head2 = FStar_Syntax_Util.unascribe head1  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____12883  ->
                      let uu____12884 = FStar_Syntax_Print.tag_of_term head2
                         in
                      let uu____12885 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____12884
                        uu____12885);
                 (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                  let uu____12887 =
                    let uu____12888 = FStar_Syntax_Subst.compress head3  in
                    uu____12888.FStar_Syntax_Syntax.n  in
                  match uu____12887 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let ed =
                        let uu____12906 =
                          FStar_TypeChecker_Env.norm_eff_name
                            cfg.FStar_TypeChecker_Cfg.tcenv m
                           in
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv uu____12906
                         in
                      let uu____12907 = ed.FStar_Syntax_Syntax.bind_repr  in
                      (match uu____12907 with
                       | (uu____12908,bind_repr) ->
                           (match lb.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____12918 ->
                                failwith
                                  "Cannot reify a top-level let binding"
                            | FStar_Util.Inl x ->
                                let is_return e =
                                  let uu____12928 =
                                    let uu____12929 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____12929.FStar_Syntax_Syntax.n  in
                                  match uu____12928 with
                                  | FStar_Syntax_Syntax.Tm_meta
                                      (e1,FStar_Syntax_Syntax.Meta_monadic
                                       (uu____12935,uu____12936))
                                      ->
                                      let uu____12945 =
                                        let uu____12946 =
                                          FStar_Syntax_Subst.compress e1  in
                                        uu____12946.FStar_Syntax_Syntax.n  in
                                      (match uu____12945 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                            (uu____12952,msrc,uu____12954))
                                           when
                                           FStar_Syntax_Util.is_pure_effect
                                             msrc
                                           ->
                                           let uu____12963 =
                                             FStar_Syntax_Subst.compress e2
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____12963
                                       | uu____12964 ->
                                           FStar_Pervasives_Native.None)
                                  | uu____12965 ->
                                      FStar_Pervasives_Native.None
                                   in
                                let uu____12966 =
                                  is_return lb.FStar_Syntax_Syntax.lbdef  in
                                (match uu____12966 with
                                 | FStar_Pervasives_Native.Some e ->
                                     let lb1 =
                                       let uu___320_12971 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___320_12971.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___320_12971.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           (uu___320_12971.FStar_Syntax_Syntax.lbtyp);
                                         FStar_Syntax_Syntax.lbeff =
                                           FStar_Parser_Const.effect_PURE_lid;
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___320_12971.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___320_12971.FStar_Syntax_Syntax.lbpos)
                                       }  in
                                     let uu____12972 = FStar_List.tl stack
                                        in
                                     let uu____12973 =
                                       let uu____12974 =
                                         let uu____12981 =
                                           let uu____12982 =
                                             let uu____12995 =
                                               FStar_Syntax_Util.mk_reify
                                                 body
                                                in
                                             ((false, [lb1]), uu____12995)
                                              in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____12982
                                            in
                                         FStar_Syntax_Syntax.mk uu____12981
                                          in
                                       uu____12974
                                         FStar_Pervasives_Native.None
                                         head3.FStar_Syntax_Syntax.pos
                                        in
                                     norm cfg env uu____12972 uu____12973
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____13011 =
                                       let uu____13012 = is_return body  in
                                       match uu____13012 with
                                       | FStar_Pervasives_Native.Some
                                           {
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_bvar y;
                                             FStar_Syntax_Syntax.pos =
                                               uu____13016;
                                             FStar_Syntax_Syntax.vars =
                                               uu____13017;_}
                                           -> FStar_Syntax_Syntax.bv_eq x y
                                       | uu____13020 -> false  in
                                     if uu____13011
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
                                          let uu____13041 =
                                            let uu____13048 =
                                              let uu____13049 =
                                                let uu____13068 =
                                                  let uu____13077 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____13077]  in
                                                (uu____13068, body1,
                                                  (FStar_Pervasives_Native.Some
                                                     body_rc))
                                                 in
                                              FStar_Syntax_Syntax.Tm_abs
                                                uu____13049
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____13048
                                             in
                                          uu____13041
                                            FStar_Pervasives_Native.None
                                            body1.FStar_Syntax_Syntax.pos
                                           in
                                        let close1 = closure_as_term cfg env
                                           in
                                        let bind_inst =
                                          let uu____13119 =
                                            let uu____13120 =
                                              FStar_Syntax_Subst.compress
                                                bind_repr
                                               in
                                            uu____13120.FStar_Syntax_Syntax.n
                                             in
                                          match uu____13119 with
                                          | FStar_Syntax_Syntax.Tm_uinst
                                              (bind1,uu____13126::uu____13127::[])
                                              ->
                                              let uu____13132 =
                                                let uu____13139 =
                                                  let uu____13140 =
                                                    let uu____13147 =
                                                      let uu____13148 =
                                                        let uu____13149 =
                                                          close1
                                                            lb.FStar_Syntax_Syntax.lbtyp
                                                           in
                                                        (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.FStar_TypeChecker_Cfg.tcenv
                                                          uu____13149
                                                         in
                                                      let uu____13150 =
                                                        let uu____13153 =
                                                          let uu____13154 =
                                                            close1 t  in
                                                          (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                            cfg.FStar_TypeChecker_Cfg.tcenv
                                                            uu____13154
                                                           in
                                                        [uu____13153]  in
                                                      uu____13148 ::
                                                        uu____13150
                                                       in
                                                    (bind1, uu____13147)  in
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                    uu____13140
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____13139
                                                 in
                                              uu____13132
                                                FStar_Pervasives_Native.None
                                                rng
                                          | uu____13160 ->
                                              failwith
                                                "NIY : Reification of indexed effects"
                                           in
                                        let maybe_range_arg =
                                          let uu____13174 =
                                            FStar_Util.for_some
                                              (FStar_Syntax_Util.attr_eq
                                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                                              ed.FStar_Syntax_Syntax.eff_attrs
                                             in
                                          if uu____13174
                                          then
                                            let uu____13185 =
                                              let uu____13194 =
                                                FStar_TypeChecker_Cfg.embed_simple
                                                  FStar_Syntax_Embeddings.e_range
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____13194
                                               in
                                            let uu____13195 =
                                              let uu____13206 =
                                                let uu____13215 =
                                                  FStar_TypeChecker_Cfg.embed_simple
                                                    FStar_Syntax_Embeddings.e_range
                                                    body2.FStar_Syntax_Syntax.pos
                                                    body2.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Syntax_Syntax.as_arg
                                                  uu____13215
                                                 in
                                              [uu____13206]  in
                                            uu____13185 :: uu____13195
                                          else []  in
                                        let reified =
                                          let uu____13252 =
                                            let uu____13259 =
                                              let uu____13260 =
                                                let uu____13277 =
                                                  let uu____13288 =
                                                    let uu____13299 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        lb.FStar_Syntax_Syntax.lbtyp
                                                       in
                                                    let uu____13308 =
                                                      let uu____13319 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          t
                                                         in
                                                      [uu____13319]  in
                                                    uu____13299 ::
                                                      uu____13308
                                                     in
                                                  let uu____13352 =
                                                    let uu____13363 =
                                                      let uu____13374 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          FStar_Syntax_Syntax.tun
                                                         in
                                                      let uu____13383 =
                                                        let uu____13394 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            head4
                                                           in
                                                        let uu____13403 =
                                                          let uu____13414 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          let uu____13423 =
                                                            let uu____13434 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                body2
                                                               in
                                                            [uu____13434]  in
                                                          uu____13414 ::
                                                            uu____13423
                                                           in
                                                        uu____13394 ::
                                                          uu____13403
                                                         in
                                                      uu____13374 ::
                                                        uu____13383
                                                       in
                                                    FStar_List.append
                                                      maybe_range_arg
                                                      uu____13363
                                                     in
                                                  FStar_List.append
                                                    uu____13288 uu____13352
                                                   in
                                                (bind_inst, uu____13277)  in
                                              FStar_Syntax_Syntax.Tm_app
                                                uu____13260
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____13259
                                             in
                                          uu____13252
                                            FStar_Pervasives_Native.None rng
                                           in
                                        FStar_TypeChecker_Cfg.log cfg
                                          (fun uu____13518  ->
                                             let uu____13519 =
                                               FStar_Syntax_Print.term_to_string
                                                 head0
                                                in
                                             let uu____13520 =
                                               FStar_Syntax_Print.term_to_string
                                                 reified
                                                in
                                             FStar_Util.print2
                                               "Reified (1) <%s> to %s\n"
                                               uu____13519 uu____13520);
                                        (let uu____13521 =
                                           FStar_List.tl stack  in
                                         norm cfg env uu____13521 reified)))))
                  | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                      ((let uu____13549 = FStar_Options.defensive ()  in
                        if uu____13549
                        then
                          let is_arg_impure uu____13561 =
                            match uu____13561 with
                            | (e,q) ->
                                let uu____13574 =
                                  let uu____13575 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____13575.FStar_Syntax_Syntax.n  in
                                (match uu____13574 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____13590 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____13590
                                 | uu____13591 -> false)
                             in
                          let uu____13592 =
                            let uu____13593 =
                              let uu____13604 =
                                FStar_Syntax_Syntax.as_arg head_app  in
                              uu____13604 :: args  in
                            FStar_Util.for_some is_arg_impure uu____13593  in
                          (if uu____13592
                           then
                             let uu____13629 =
                               let uu____13634 =
                                 let uu____13635 =
                                   FStar_Syntax_Print.term_to_string head3
                                    in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____13635
                                  in
                               (FStar_Errors.Warning_Defensive, uu____13634)
                                in
                             FStar_Errors.log_issue
                               head3.FStar_Syntax_Syntax.pos uu____13629
                           else ())
                        else ());
                       (let fallback1 uu____13643 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____13647  ->
                               let uu____13648 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____13648 "");
                          (let uu____13649 = FStar_List.tl stack  in
                           let uu____13650 = FStar_Syntax_Util.mk_reify head3
                              in
                           norm cfg env uu____13649 uu____13650)
                           in
                        let fallback2 uu____13656 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____13660  ->
                               let uu____13661 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____13661 "");
                          (let uu____13662 = FStar_List.tl stack  in
                           let uu____13663 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (head3,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               head0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env uu____13662 uu____13663)
                           in
                        let uu____13668 =
                          let uu____13669 =
                            FStar_Syntax_Util.un_uinst head_app  in
                          uu____13669.FStar_Syntax_Syntax.n  in
                        match uu____13668 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____13675 =
                              let uu____13676 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____13676  in
                            if uu____13675
                            then fallback1 ()
                            else
                              (let uu____13678 =
                                 let uu____13679 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____13679  in
                               if uu____13678
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____13694 =
                                      let uu____13699 =
                                        FStar_Syntax_Util.mk_reify head_app
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____13699 args
                                       in
                                    uu____13694 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____13702 = FStar_List.tl stack  in
                                  norm cfg env uu____13702 t1))
                        | uu____13703 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____13705) ->
                      do_reify_monadic fallback cfg env stack e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____13729 = closure_as_term cfg env t'  in
                        reify_lift cfg e msrc mtgt uu____13729  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____13733  ->
                            let uu____13734 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____13734);
                       (let uu____13735 = FStar_List.tl stack  in
                        norm cfg env uu____13735 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                      let branches1 =
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun uu____13856  ->
                                match uu____13856 with
                                | (pat,wopt,tm) ->
                                    let uu____13904 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____13904)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                          head3.FStar_Syntax_Syntax.pos
                         in
                      let uu____13936 = FStar_List.tl stack  in
                      norm cfg env uu____13936 tm
                  | uu____13937 -> fallback ()))

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
              (fun uu____13951  ->
                 let uu____13952 = FStar_Ident.string_of_lid msrc  in
                 let uu____13953 = FStar_Ident.string_of_lid mtgt  in
                 let uu____13954 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____13952
                   uu____13953 uu____13954);
            (let uu____13955 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____13955
             then
               let ed =
                 let uu____13957 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____13957  in
               let uu____13958 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____13958 with
               | (uu____13959,return_repr) ->
                   let return_inst =
                     let uu____13972 =
                       let uu____13973 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____13973.FStar_Syntax_Syntax.n  in
                     match uu____13972 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____13979::[]) ->
                         let uu____13984 =
                           let uu____13991 =
                             let uu____13992 =
                               let uu____13999 =
                                 let uu____14000 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____14000]  in
                               (return_tm, uu____13999)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____13992  in
                           FStar_Syntax_Syntax.mk uu____13991  in
                         uu____13984 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____14006 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____14009 =
                     let uu____14016 =
                       let uu____14017 =
                         let uu____14034 =
                           let uu____14045 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____14054 =
                             let uu____14065 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____14065]  in
                           uu____14045 :: uu____14054  in
                         (return_inst, uu____14034)  in
                       FStar_Syntax_Syntax.Tm_app uu____14017  in
                     FStar_Syntax_Syntax.mk uu____14016  in
                   uu____14009 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____14114 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____14114 with
                | FStar_Pervasives_Native.None  ->
                    let uu____14117 =
                      let uu____14118 = FStar_Ident.text_of_lid msrc  in
                      let uu____14119 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____14118 uu____14119
                       in
                    failwith uu____14117
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14120;
                      FStar_TypeChecker_Env.mtarget = uu____14121;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14122;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____14144 =
                      let uu____14145 = FStar_Ident.text_of_lid msrc  in
                      let uu____14146 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____14145 uu____14146
                       in
                    failwith uu____14144
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____14147;
                      FStar_TypeChecker_Env.mtarget = uu____14148;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____14149;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____14184 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____14185 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____14184 t FStar_Syntax_Syntax.tun uu____14185))

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
                (fun uu____14255  ->
                   match uu____14255 with
                   | (a,imp) ->
                       let uu____14274 = norm cfg env [] a  in
                       (uu____14274, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____14284  ->
             let uu____14285 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____14286 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____14285 uu____14286);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____14310 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____14310
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___321_14313 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___321_14313.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___321_14313.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____14335 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____14335
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___322_14338 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___322_14338.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___322_14338.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____14383  ->
                      match uu____14383 with
                      | (a,i) ->
                          let uu____14402 = norm cfg env [] a  in
                          (uu____14402, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___266_14424  ->
                       match uu___266_14424 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____14428 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____14428
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___323_14436 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___324_14439 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___324_14439.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___323_14436.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___323_14436.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun b  ->
        let uu____14443 = b  in
        match uu____14443 with
        | (x,imp) ->
            let x1 =
              let uu___325_14451 = x  in
              let uu____14452 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___325_14451.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___325_14451.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____14452
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____14463 =
                    let uu____14464 = closure_as_term cfg env t  in
                    FStar_Syntax_Syntax.Meta uu____14464  in
                  FStar_Pervasives_Native.Some uu____14463
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____14475 =
          FStar_List.fold_left
            (fun uu____14509  ->
               fun b  ->
                 match uu____14509 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____14475 with | (nbs,uu____14589) -> FStar_List.rev nbs

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
            let uu____14621 =
              let uu___326_14622 = rc  in
              let uu____14623 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___326_14622.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____14623;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___326_14622.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____14621
        | uu____14632 -> lopt

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
            (let uu____14641 = FStar_Syntax_Print.term_to_string tm  in
             let uu____14642 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____14641 uu____14642)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___267_14646  ->
      match uu___267_14646 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____14659 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____14659 with
           | FStar_Pervasives_Native.Some (t,uu____14667) -> t
           | FStar_Pervasives_Native.None  ->
               let uu____14676 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____14676)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____14684 = norm_cb cfg  in
            reduce_primops uu____14684 cfg env tm  in
          let uu____14691 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____14691
          then tm1
          else
            (let w t =
               let uu___327_14705 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___327_14705.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___327_14705.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____14716 =
                 let uu____14717 = FStar_Syntax_Util.unmeta t  in
                 uu____14717.FStar_Syntax_Syntax.n  in
               match uu____14716 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____14724 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____14785)::args1,(bv,uu____14788)::bs1) ->
                   let uu____14842 =
                     let uu____14843 = FStar_Syntax_Subst.compress t  in
                     uu____14843.FStar_Syntax_Syntax.n  in
                   (match uu____14842 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____14847 -> false)
               | ([],[]) -> true
               | (uu____14876,uu____14877) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____14926 = FStar_Syntax_Print.term_to_string t  in
                  let uu____14927 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____14926
                    uu____14927)
               else ();
               (let uu____14929 = FStar_Syntax_Util.head_and_args' t  in
                match uu____14929 with
                | (hd1,args) ->
                    let uu____14968 =
                      let uu____14969 = FStar_Syntax_Subst.compress hd1  in
                      uu____14969.FStar_Syntax_Syntax.n  in
                    (match uu____14968 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____14976 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____14977 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____14978 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____14976 uu____14977 uu____14978)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____14980 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____14997 = FStar_Syntax_Print.term_to_string t  in
                  let uu____14998 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____14997
                    uu____14998)
               else ();
               (let uu____15000 = FStar_Syntax_Util.is_squash t  in
                match uu____15000 with
                | FStar_Pervasives_Native.Some (uu____15011,t') ->
                    is_applied bs t'
                | uu____15023 ->
                    let uu____15032 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____15032 with
                     | FStar_Pervasives_Native.Some (uu____15043,t') ->
                         is_applied bs t'
                     | uu____15055 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____15079 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____15079 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____15086)::(q,uu____15088)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____15130 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____15131 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____15130 uu____15131)
                    else ();
                    (let uu____15133 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____15133 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____15138 =
                           let uu____15139 = FStar_Syntax_Subst.compress p
                              in
                           uu____15139.FStar_Syntax_Syntax.n  in
                         (match uu____15138 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____15147 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____15147))
                          | uu____15150 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____15153)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____15178 =
                           let uu____15179 = FStar_Syntax_Subst.compress p1
                              in
                           uu____15179.FStar_Syntax_Syntax.n  in
                         (match uu____15178 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____15187 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____15187))
                          | uu____15190 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____15194 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____15194 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____15199 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____15199 with
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
                                     let uu____15210 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____15210))
                               | uu____15213 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____15218)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____15243 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____15243 with
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
                                     let uu____15254 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____15254))
                               | uu____15257 -> FStar_Pervasives_Native.None)
                          | uu____15260 -> FStar_Pervasives_Native.None)
                     | uu____15263 -> FStar_Pervasives_Native.None))
               | uu____15266 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____15279 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____15279 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____15285)::[],uu____15286,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____15305 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____15306 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____15305
                         uu____15306)
                    else ();
                    is_quantified_const bv phi')
               | uu____15308 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____15321 =
                 let uu____15322 = FStar_Syntax_Subst.compress phi  in
                 uu____15322.FStar_Syntax_Syntax.n  in
               match uu____15321 with
               | FStar_Syntax_Syntax.Tm_match (uu____15327,br::brs) ->
                   let uu____15394 = br  in
                   (match uu____15394 with
                    | (uu____15411,uu____15412,e) ->
                        let r =
                          let uu____15433 = simp_t e  in
                          match uu____15433 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____15439 =
                                FStar_List.for_all
                                  (fun uu____15457  ->
                                     match uu____15457 with
                                     | (uu____15470,uu____15471,e') ->
                                         let uu____15485 = simp_t e'  in
                                         uu____15485 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____15439
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____15493 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____15502 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____15502
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____15537 =
                 match uu____15537 with
                 | (t1,q) ->
                     let uu____15558 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____15558 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____15590 -> (t1, q))
                  in
               let uu____15603 = FStar_Syntax_Util.head_and_args t  in
               match uu____15603 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____15681 =
                 let uu____15682 = FStar_Syntax_Util.unmeta ty  in
                 uu____15682.FStar_Syntax_Syntax.n  in
               match uu____15681 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____15686) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____15691,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____15715 -> false  in
             let simplify1 arg =
               let uu____15746 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____15746, arg)  in
             let uu____15759 = is_forall_const tm1  in
             match uu____15759 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____15764 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____15765 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____15764
                       uu____15765)
                  else ();
                  (let uu____15767 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____15767))
             | FStar_Pervasives_Native.None  ->
                 let uu____15768 =
                   let uu____15769 = FStar_Syntax_Subst.compress tm1  in
                   uu____15769.FStar_Syntax_Syntax.n  in
                 (match uu____15768 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____15773;
                              FStar_Syntax_Syntax.vars = uu____15774;_},uu____15775);
                         FStar_Syntax_Syntax.pos = uu____15776;
                         FStar_Syntax_Syntax.vars = uu____15777;_},args)
                      ->
                      let uu____15807 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____15807
                      then
                        let uu____15808 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____15808 with
                         | (FStar_Pervasives_Native.Some (true ),uu____15863)::
                             (uu____15864,(arg,uu____15866))::[] ->
                             maybe_auto_squash arg
                         | (uu____15931,(arg,uu____15933))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____15934)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____15999)::uu____16000::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____16063::(FStar_Pervasives_Native.Some (false
                                         ),uu____16064)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____16127 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____16143 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____16143
                         then
                           let uu____16144 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____16144 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____16199)::uu____16200::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____16263::(FStar_Pervasives_Native.Some (true
                                           ),uu____16264)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____16327)::(uu____16328,(arg,uu____16330))::[]
                               -> maybe_auto_squash arg
                           | (uu____16395,(arg,uu____16397))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____16398)::[]
                               -> maybe_auto_squash arg
                           | uu____16463 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____16479 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____16479
                            then
                              let uu____16480 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____16480 with
                              | uu____16535::(FStar_Pervasives_Native.Some
                                              (true ),uu____16536)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____16599)::uu____16600::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____16663)::(uu____16664,(arg,uu____16666))::[]
                                  -> maybe_auto_squash arg
                              | (uu____16731,(p,uu____16733))::(uu____16734,
                                                                (q,uu____16736))::[]
                                  ->
                                  let uu____16801 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____16801
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____16803 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____16819 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____16819
                               then
                                 let uu____16820 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____16820 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16875)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____16876)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____16941)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____16942)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17007)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____17008)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17073)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17074)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____17139,(arg,uu____17141))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____17142)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17207)::(uu____17208,(arg,uu____17210))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____17275,(arg,uu____17277))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____17278)::[]
                                     ->
                                     let uu____17343 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17343
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17344)::(uu____17345,(arg,uu____17347))::[]
                                     ->
                                     let uu____17412 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____17412
                                 | (uu____17413,(p,uu____17415))::(uu____17416,
                                                                   (q,uu____17418))::[]
                                     ->
                                     let uu____17483 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____17483
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____17485 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____17501 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____17501
                                  then
                                    let uu____17502 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____17502 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____17557)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____17596)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____17635 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____17651 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____17651
                                     then
                                       match args with
                                       | (t,uu____17653)::[] ->
                                           let uu____17678 =
                                             let uu____17679 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17679.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17678 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17682::[],body,uu____17684)
                                                ->
                                                let uu____17719 = simp_t body
                                                   in
                                                (match uu____17719 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____17722 -> tm1)
                                            | uu____17725 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____17727))::(t,uu____17729)::[]
                                           ->
                                           let uu____17768 =
                                             let uu____17769 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____17769.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____17768 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____17772::[],body,uu____17774)
                                                ->
                                                let uu____17809 = simp_t body
                                                   in
                                                (match uu____17809 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____17812 -> tm1)
                                            | uu____17815 -> tm1)
                                       | uu____17816 -> tm1
                                     else
                                       (let uu____17828 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____17828
                                        then
                                          match args with
                                          | (t,uu____17830)::[] ->
                                              let uu____17855 =
                                                let uu____17856 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17856.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17855 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17859::[],body,uu____17861)
                                                   ->
                                                   let uu____17896 =
                                                     simp_t body  in
                                                   (match uu____17896 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____17899 -> tm1)
                                               | uu____17902 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____17904))::(t,uu____17906)::[]
                                              ->
                                              let uu____17945 =
                                                let uu____17946 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____17946.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____17945 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____17949::[],body,uu____17951)
                                                   ->
                                                   let uu____17986 =
                                                     simp_t body  in
                                                   (match uu____17986 with
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
                                                    | uu____17989 -> tm1)
                                               | uu____17992 -> tm1)
                                          | uu____17993 -> tm1
                                        else
                                          (let uu____18005 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____18005
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18006;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18007;_},uu____18008)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18033;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18034;_},uu____18035)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____18060 -> tm1
                                           else
                                             (let uu____18072 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____18072 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____18092 ->
                                                  let uu____18101 =
                                                    let uu____18108 =
                                                      norm_cb cfg  in
                                                    reduce_equality
                                                      uu____18108 cfg env
                                                     in
                                                  uu____18101 tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____18116;
                         FStar_Syntax_Syntax.vars = uu____18117;_},args)
                      ->
                      let uu____18143 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18143
                      then
                        let uu____18144 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18144 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18199)::
                             (uu____18200,(arg,uu____18202))::[] ->
                             maybe_auto_squash arg
                         | (uu____18267,(arg,uu____18269))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18270)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18335)::uu____18336::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18399::(FStar_Pervasives_Native.Some (false
                                         ),uu____18400)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18463 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18479 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18479
                         then
                           let uu____18480 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18480 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18535)::uu____18536::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18599::(FStar_Pervasives_Native.Some (true
                                           ),uu____18600)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18663)::(uu____18664,(arg,uu____18666))::[]
                               -> maybe_auto_squash arg
                           | (uu____18731,(arg,uu____18733))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18734)::[]
                               -> maybe_auto_squash arg
                           | uu____18799 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18815 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____18815
                            then
                              let uu____18816 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____18816 with
                              | uu____18871::(FStar_Pervasives_Native.Some
                                              (true ),uu____18872)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____18935)::uu____18936::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____18999)::(uu____19000,(arg,uu____19002))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19067,(p,uu____19069))::(uu____19070,
                                                                (q,uu____19072))::[]
                                  ->
                                  let uu____19137 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19137
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19139 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19155 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19155
                               then
                                 let uu____19156 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19156 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19211)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19212)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19277)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19278)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19343)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19344)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19409)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19410)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19475,(arg,uu____19477))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19478)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19543)::(uu____19544,(arg,uu____19546))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19611,(arg,uu____19613))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19614)::[]
                                     ->
                                     let uu____19679 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19679
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19680)::(uu____19681,(arg,uu____19683))::[]
                                     ->
                                     let uu____19748 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19748
                                 | (uu____19749,(p,uu____19751))::(uu____19752,
                                                                   (q,uu____19754))::[]
                                     ->
                                     let uu____19819 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19819
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19821 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19837 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19837
                                  then
                                    let uu____19838 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19838 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19893)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19932)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19971 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19987 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19987
                                     then
                                       match args with
                                       | (t,uu____19989)::[] ->
                                           let uu____20014 =
                                             let uu____20015 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20015.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20014 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20018::[],body,uu____20020)
                                                ->
                                                let uu____20055 = simp_t body
                                                   in
                                                (match uu____20055 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20058 -> tm1)
                                            | uu____20061 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20063))::(t,uu____20065)::[]
                                           ->
                                           let uu____20104 =
                                             let uu____20105 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20105.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20104 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20108::[],body,uu____20110)
                                                ->
                                                let uu____20145 = simp_t body
                                                   in
                                                (match uu____20145 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20148 -> tm1)
                                            | uu____20151 -> tm1)
                                       | uu____20152 -> tm1
                                     else
                                       (let uu____20164 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20164
                                        then
                                          match args with
                                          | (t,uu____20166)::[] ->
                                              let uu____20191 =
                                                let uu____20192 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20192.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20191 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20195::[],body,uu____20197)
                                                   ->
                                                   let uu____20232 =
                                                     simp_t body  in
                                                   (match uu____20232 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20235 -> tm1)
                                               | uu____20238 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20240))::(t,uu____20242)::[]
                                              ->
                                              let uu____20281 =
                                                let uu____20282 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20282.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20281 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20285::[],body,uu____20287)
                                                   ->
                                                   let uu____20322 =
                                                     simp_t body  in
                                                   (match uu____20322 with
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
                                                    | uu____20325 -> tm1)
                                               | uu____20328 -> tm1)
                                          | uu____20329 -> tm1
                                        else
                                          (let uu____20341 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20341
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20342;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20343;_},uu____20344)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20369;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20370;_},uu____20371)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20396 -> tm1
                                           else
                                             (let uu____20408 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____20408 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____20428 ->
                                                  let uu____20437 =
                                                    let uu____20444 =
                                                      norm_cb cfg  in
                                                    reduce_equality
                                                      uu____20444 cfg env
                                                     in
                                                  uu____20437 tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____20457 = simp_t t  in
                      (match uu____20457 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____20460 ->
                      let uu____20483 = is_const_match tm1  in
                      (match uu____20483 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____20486 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____20496  ->
               (let uu____20498 = FStar_Syntax_Print.tag_of_term t  in
                let uu____20499 = FStar_Syntax_Print.term_to_string t  in
                let uu____20500 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____20507 =
                  let uu____20508 =
                    let uu____20511 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____20511
                     in
                  stack_to_string uu____20508  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____20498 uu____20499 uu____20500 uu____20507);
               (let uu____20534 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____20534
                then
                  let uu____20535 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____20535 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____20542 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____20543 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____20544 =
                          let uu____20545 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____20545
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____20542
                          uu____20543 uu____20544);
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
                   let uu____20563 =
                     let uu____20564 =
                       let uu____20565 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____20565  in
                     FStar_Util.string_of_int uu____20564  in
                   let uu____20570 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____20571 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____20563 uu____20570 uu____20571)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____20577,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                FStar_TypeChecker_Cfg.log cfg
                  (fun uu____20628  ->
                     let uu____20629 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____20629);
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
               let uu____20667 =
                 let uu___328_20668 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___328_20668.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___328_20668.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____20667
           | (Arg (Univ uu____20671,uu____20672,uu____20673))::uu____20674 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____20677,uu____20678))::uu____20679 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____20694,uu____20695),aq,r))::stack1
               when
               let uu____20745 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____20745 ->
               let t2 =
                 let uu____20749 =
                   let uu____20754 =
                     let uu____20755 = closure_as_term cfg env_arg tm  in
                     (uu____20755, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____20754  in
                 uu____20749 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____20767),aq,r))::stack1 ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____20820  ->
                     let uu____20821 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____20821);
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
                  (let uu____20835 = FStar_ST.op_Bang m  in
                   match uu____20835 with
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
                   | FStar_Pervasives_Native.Some (uu____20976,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____21031 =
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____21035  ->
                      let uu____21036 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____21036);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____21044 =
                 let uu____21045 = FStar_Syntax_Subst.compress t1  in
                 uu____21045.FStar_Syntax_Syntax.n  in
               (match uu____21044 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____21072 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____21072  in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____21076  ->
                          let uu____21077 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____21077);
                     (let uu____21078 = FStar_List.tl stack  in
                      norm cfg env1 uu____21078 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____21079);
                       FStar_Syntax_Syntax.pos = uu____21080;
                       FStar_Syntax_Syntax.vars = uu____21081;_},(e,uu____21083)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____21122 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                    ->
                    let uu____21139 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____21139 with
                     | (hd1,args) ->
                         let uu____21182 =
                           let uu____21183 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____21183.FStar_Syntax_Syntax.n  in
                         (match uu____21182 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____21187 =
                                FStar_TypeChecker_Cfg.find_prim_step cfg fv
                                 in
                              (match uu____21187 with
                               | FStar_Pervasives_Native.Some
                                   {
                                     FStar_TypeChecker_Cfg.name = uu____21190;
                                     FStar_TypeChecker_Cfg.arity =
                                       uu____21191;
                                     FStar_TypeChecker_Cfg.univ_arity =
                                       uu____21192;
                                     FStar_TypeChecker_Cfg.auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     FStar_TypeChecker_Cfg.strong_reduction_ok
                                       = uu____21194;
                                     FStar_TypeChecker_Cfg.requires_binder_substitution
                                       = uu____21195;
                                     FStar_TypeChecker_Cfg.interpretation =
                                       uu____21196;
                                     FStar_TypeChecker_Cfg.interpretation_nbe
                                       = uu____21197;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____21227 -> fallback " (3)" ())
                          | uu____21230 -> fallback " (4)" ()))
                | uu____21231 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (FStar_TypeChecker_Cfg.log cfg1
                  (fun uu____21256  ->
                     let uu____21257 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____21257);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____21266 =
                   FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____21271  ->
                        let uu____21272 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____21273 =
                          let uu____21274 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____21301  ->
                                    match uu____21301 with
                                    | (p,uu____21311,uu____21312) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____21274
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____21272 uu____21273);
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
                             (fun uu___268_21329  ->
                                match uu___268_21329 with
                                | FStar_TypeChecker_Env.InliningDelta  ->
                                    true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____21330 -> false))
                         in
                      let steps =
                        let uu___329_21332 = cfg1.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___329_21332.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___329_21332.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta = false;
                          FStar_TypeChecker_Cfg.weak =
                            (uu___329_21332.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___329_21332.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___329_21332.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___329_21332.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___329_21332.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_tac = false;
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___329_21332.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___329_21332.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___329_21332.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___329_21332.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___329_21332.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___329_21332.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___329_21332.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___329_21332.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___329_21332.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___329_21332.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___329_21332.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___329_21332.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___329_21332.FStar_TypeChecker_Cfg.nbe_step)
                        }  in
                      let uu___330_21337 = cfg1  in
                      {
                        FStar_TypeChecker_Cfg.steps = steps;
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___330_21337.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___330_21337.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level = new_delta;
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___330_21337.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong = true;
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___330_21337.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___330_21337.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying =
                          (uu___330_21337.FStar_TypeChecker_Cfg.reifying)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____21409 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____21438 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____21522  ->
                                    fun uu____21523  ->
                                      match (uu____21522, uu____21523) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____21662 = norm_pat env3 p1
                                             in
                                          (match uu____21662 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____21438 with
                           | (pats1,env3) ->
                               ((let uu___331_21824 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___331_21824.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___332_21843 = x  in
                            let uu____21844 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___332_21843.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___332_21843.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21844
                            }  in
                          ((let uu___333_21858 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___333_21858.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___334_21869 = x  in
                            let uu____21870 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___334_21869.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___334_21869.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21870
                            }  in
                          ((let uu___335_21884 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___335_21884.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___336_21900 = x  in
                            let uu____21901 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___336_21900.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___336_21900.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21901
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___337_21916 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___337_21916.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____21960 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____21990 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____21990 with
                                  | (p,wopt,e) ->
                                      let uu____22010 = norm_pat env1 p  in
                                      (match uu____22010 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____22065 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____22065
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____22082 =
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
                      if uu____22082
                      then
                        norm
                          (let uu___338_22087 = cfg1  in
                           {
                             FStar_TypeChecker_Cfg.steps =
                               (let uu___339_22090 =
                                  cfg1.FStar_TypeChecker_Cfg.steps  in
                                {
                                  FStar_TypeChecker_Cfg.beta =
                                    (uu___339_22090.FStar_TypeChecker_Cfg.beta);
                                  FStar_TypeChecker_Cfg.iota =
                                    (uu___339_22090.FStar_TypeChecker_Cfg.iota);
                                  FStar_TypeChecker_Cfg.zeta =
                                    (uu___339_22090.FStar_TypeChecker_Cfg.zeta);
                                  FStar_TypeChecker_Cfg.weak =
                                    (uu___339_22090.FStar_TypeChecker_Cfg.weak);
                                  FStar_TypeChecker_Cfg.hnf =
                                    (uu___339_22090.FStar_TypeChecker_Cfg.hnf);
                                  FStar_TypeChecker_Cfg.primops =
                                    (uu___339_22090.FStar_TypeChecker_Cfg.primops);
                                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                    =
                                    (uu___339_22090.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                  FStar_TypeChecker_Cfg.unfold_until =
                                    (uu___339_22090.FStar_TypeChecker_Cfg.unfold_until);
                                  FStar_TypeChecker_Cfg.unfold_only =
                                    (uu___339_22090.FStar_TypeChecker_Cfg.unfold_only);
                                  FStar_TypeChecker_Cfg.unfold_fully =
                                    (uu___339_22090.FStar_TypeChecker_Cfg.unfold_fully);
                                  FStar_TypeChecker_Cfg.unfold_attr =
                                    (uu___339_22090.FStar_TypeChecker_Cfg.unfold_attr);
                                  FStar_TypeChecker_Cfg.unfold_tac =
                                    (uu___339_22090.FStar_TypeChecker_Cfg.unfold_tac);
                                  FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                    =
                                    (uu___339_22090.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                  FStar_TypeChecker_Cfg.simplify =
                                    (uu___339_22090.FStar_TypeChecker_Cfg.simplify);
                                  FStar_TypeChecker_Cfg.erase_universes =
                                    (uu___339_22090.FStar_TypeChecker_Cfg.erase_universes);
                                  FStar_TypeChecker_Cfg.allow_unbound_universes
                                    =
                                    (uu___339_22090.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                  FStar_TypeChecker_Cfg.reify_ =
                                    (uu___339_22090.FStar_TypeChecker_Cfg.reify_);
                                  FStar_TypeChecker_Cfg.compress_uvars =
                                    (uu___339_22090.FStar_TypeChecker_Cfg.compress_uvars);
                                  FStar_TypeChecker_Cfg.no_full_norm =
                                    (uu___339_22090.FStar_TypeChecker_Cfg.no_full_norm);
                                  FStar_TypeChecker_Cfg.check_no_uvars =
                                    (uu___339_22090.FStar_TypeChecker_Cfg.check_no_uvars);
                                  FStar_TypeChecker_Cfg.unmeta =
                                    (uu___339_22090.FStar_TypeChecker_Cfg.unmeta);
                                  FStar_TypeChecker_Cfg.unascribe =
                                    (uu___339_22090.FStar_TypeChecker_Cfg.unascribe);
                                  FStar_TypeChecker_Cfg.in_full_norm_request
                                    =
                                    (uu___339_22090.FStar_TypeChecker_Cfg.in_full_norm_request);
                                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                    = false;
                                  FStar_TypeChecker_Cfg.nbe_step =
                                    (uu___339_22090.FStar_TypeChecker_Cfg.nbe_step)
                                });
                             FStar_TypeChecker_Cfg.tcenv =
                               (uu___338_22087.FStar_TypeChecker_Cfg.tcenv);
                             FStar_TypeChecker_Cfg.debug =
                               (uu___338_22087.FStar_TypeChecker_Cfg.debug);
                             FStar_TypeChecker_Cfg.delta_level =
                               (uu___338_22087.FStar_TypeChecker_Cfg.delta_level);
                             FStar_TypeChecker_Cfg.primitive_steps =
                               (uu___338_22087.FStar_TypeChecker_Cfg.primitive_steps);
                             FStar_TypeChecker_Cfg.strong =
                               (uu___338_22087.FStar_TypeChecker_Cfg.strong);
                             FStar_TypeChecker_Cfg.memoize_lazy =
                               (uu___338_22087.FStar_TypeChecker_Cfg.memoize_lazy);
                             FStar_TypeChecker_Cfg.normalize_pure_lets =
                               (uu___338_22087.FStar_TypeChecker_Cfg.normalize_pure_lets);
                             FStar_TypeChecker_Cfg.reifying =
                               (uu___338_22087.FStar_TypeChecker_Cfg.reifying)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____22092 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____22092)
                    in
                 let rec is_cons head1 =
                   let uu____22117 =
                     let uu____22118 = FStar_Syntax_Subst.compress head1  in
                     uu____22118.FStar_Syntax_Syntax.n  in
                   match uu____22117 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____22122) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____22127 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____22128;
                         FStar_Syntax_Syntax.fv_delta = uu____22129;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____22130;
                         FStar_Syntax_Syntax.fv_delta = uu____22131;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____22132);_}
                       -> true
                   | uu____22139 -> false  in
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
                   let uu____22303 =
                     FStar_Syntax_Util.head_and_args scrutinee2  in
                   match uu____22303 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____22396 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee2.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____22435 ->
                                 let uu____22436 =
                                   let uu____22437 = is_cons head1  in
                                   Prims.op_Negation uu____22437  in
                                 FStar_Util.Inr uu____22436)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____22462 =
                              let uu____22463 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____22463.FStar_Syntax_Syntax.n  in
                            (match uu____22462 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____22481 ->
                                 let uu____22482 =
                                   let uu____22483 = is_cons head1  in
                                   Prims.op_Negation uu____22483  in
                                 FStar_Util.Inr uu____22482))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____22566)::rest_a,(p1,uu____22569)::rest_p) ->
                       let uu____22623 = matches_pat t2 p1  in
                       (match uu____22623 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____22672 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____22792 = matches_pat scrutinee1 p1  in
                       (match uu____22792 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (FStar_TypeChecker_Cfg.log cfg1
                               (fun uu____22832  ->
                                  let uu____22833 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____22834 =
                                    let uu____22835 =
                                      FStar_List.map
                                        (fun uu____22845  ->
                                           match uu____22845 with
                                           | (uu____22850,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____22835
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____22833 uu____22834);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____22882  ->
                                       match uu____22882 with
                                       | (bv,t2) ->
                                           let uu____22905 =
                                             let uu____22912 =
                                               let uu____22915 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____22915
                                                in
                                             let uu____22916 =
                                               let uu____22917 =
                                                 let uu____22948 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____22948, false)
                                                  in
                                               Clos uu____22917  in
                                             (uu____22912, uu____22916)  in
                                           uu____22905 :: env2) env1 s
                                 in
                              let uu____23061 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____23061)))
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
            (fun uu____23091  ->
               let uu____23092 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____23092);
          (let uu____23093 = is_nbe_request s  in
           if uu____23093
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____23097  ->
                   let uu____23098 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____23098);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____23102  ->
                   let uu____23103 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____23103);
              (let r = nbe_eval c s t  in
               FStar_TypeChecker_Cfg.log_top c
                 (fun uu____23108  ->
                    let uu____23109 = FStar_Syntax_Print.term_to_string r  in
                    FStar_Util.print1 "}\nNormalization result = (%s)\n"
                      uu____23109);
               r))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____23114  ->
                   let uu____23115 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____23115);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____23119  ->
                   let uu____23120 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____23120);
              (let r = norm c [] [] t  in
               FStar_TypeChecker_Cfg.log_top c
                 (fun uu____23131  ->
                    let uu____23132 = FStar_Syntax_Print.term_to_string r  in
                    FStar_Util.print1 "}\nNormalization result = (%s)\n"
                      uu____23132);
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
        let uu____23163 = FStar_TypeChecker_Cfg.config s e  in
        norm_comp uu____23163 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____23180 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____23180 [] u
  
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
        let uu____23204 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____23204  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____23211 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___340_23230 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___340_23230.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___340_23230.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name
              cfg.FStar_TypeChecker_Cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____23237 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____23237
          then
            let ct1 =
              let uu____23239 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____23239 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____23246 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____23246
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___341_23250 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___341_23250.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___341_23250.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___341_23250.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev
                      cfg.FStar_TypeChecker_Cfg.tcenv c
                     in
                  let uu___342_23252 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___342_23252.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___342_23252.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___342_23252.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___342_23252.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___343_23253 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___343_23253.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___343_23253.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____23255 -> c
  
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
        let uu____23273 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____23273  in
      let uu____23280 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____23280
      then
        let uu____23281 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____23281 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____23287  ->
                 let uu____23288 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____23288)
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
          (fun uu___345_23302  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___344_23305 ->
            ((let uu____23307 =
                let uu____23312 =
                  let uu____23313 = FStar_Util.message_of_exn uu___344_23305
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23313
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____23312)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____23307);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          (fun uu___347_23327  ->
             match () with
             | () ->
                 let uu____23328 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____23328 [] c) ()
        with
        | uu___346_23337 ->
            ((let uu____23339 =
                let uu____23344 =
                  let uu____23345 = FStar_Util.message_of_exn uu___346_23337
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____23345
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____23344)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____23339);
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
                   let uu____23390 =
                     let uu____23391 =
                       let uu____23398 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____23398)  in
                     FStar_Syntax_Syntax.Tm_refine uu____23391  in
                   mk uu____23390 t01.FStar_Syntax_Syntax.pos
               | uu____23403 -> t2)
          | uu____23404 -> t2  in
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
        let uu____23485 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____23485 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____23522 ->
                 let uu____23531 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____23531 with
                  | (actuals,uu____23541,uu____23542) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____23560 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____23560 with
                         | (binders,args) ->
                             let uu____23571 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____23571
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
      | uu____23585 ->
          let uu____23586 = FStar_Syntax_Util.head_and_args t  in
          (match uu____23586 with
           | (head1,args) ->
               let uu____23629 =
                 let uu____23630 = FStar_Syntax_Subst.compress head1  in
                 uu____23630.FStar_Syntax_Syntax.n  in
               (match uu____23629 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____23651 =
                      let uu____23666 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____23666  in
                    (match uu____23651 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____23704 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___348_23712 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___348_23712.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___348_23712.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___348_23712.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___348_23712.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___348_23712.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___348_23712.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___348_23712.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___348_23712.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___348_23712.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___348_23712.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___348_23712.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___348_23712.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___348_23712.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___348_23712.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___348_23712.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___348_23712.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___348_23712.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___348_23712.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___348_23712.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___348_23712.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___348_23712.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___348_23712.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___348_23712.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___348_23712.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___348_23712.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___348_23712.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___348_23712.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___348_23712.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___348_23712.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___348_23712.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___348_23712.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___348_23712.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___348_23712.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___348_23712.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___348_23712.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___348_23712.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___348_23712.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___348_23712.FStar_TypeChecker_Env.nbe)
                                 }) t
                               in
                            match uu____23704 with
                            | (uu____23713,ty,uu____23715) ->
                                eta_expand_with_type env t ty))
                | uu____23716 ->
                    let uu____23717 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___349_23725 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___349_23725.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___349_23725.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___349_23725.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___349_23725.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___349_23725.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___349_23725.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___349_23725.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___349_23725.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___349_23725.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___349_23725.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___349_23725.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___349_23725.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___349_23725.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___349_23725.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___349_23725.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___349_23725.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___349_23725.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___349_23725.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___349_23725.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___349_23725.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___349_23725.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___349_23725.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___349_23725.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___349_23725.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___349_23725.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___349_23725.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___349_23725.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___349_23725.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___349_23725.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___349_23725.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___349_23725.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___349_23725.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___349_23725.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___349_23725.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___349_23725.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___349_23725.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___349_23725.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___349_23725.FStar_TypeChecker_Env.nbe)
                         }) t
                       in
                    (match uu____23717 with
                     | (uu____23726,ty,uu____23728) ->
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
      let uu___350_23809 = x  in
      let uu____23810 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___350_23809.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___350_23809.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____23810
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____23813 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____23836 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____23837 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____23838 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____23839 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____23846 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____23847 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____23848 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___351_23882 = rc  in
          let uu____23883 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____23892 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___351_23882.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____23883;
            FStar_Syntax_Syntax.residual_flags = uu____23892
          }  in
        let uu____23895 =
          let uu____23896 =
            let uu____23915 = elim_delayed_subst_binders bs  in
            let uu____23924 = elim_delayed_subst_term t2  in
            let uu____23927 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____23915, uu____23924, uu____23927)  in
          FStar_Syntax_Syntax.Tm_abs uu____23896  in
        mk1 uu____23895
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____23964 =
          let uu____23965 =
            let uu____23980 = elim_delayed_subst_binders bs  in
            let uu____23989 = elim_delayed_subst_comp c  in
            (uu____23980, uu____23989)  in
          FStar_Syntax_Syntax.Tm_arrow uu____23965  in
        mk1 uu____23964
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____24008 =
          let uu____24009 =
            let uu____24016 = elim_bv bv  in
            let uu____24017 = elim_delayed_subst_term phi  in
            (uu____24016, uu____24017)  in
          FStar_Syntax_Syntax.Tm_refine uu____24009  in
        mk1 uu____24008
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____24048 =
          let uu____24049 =
            let uu____24066 = elim_delayed_subst_term t2  in
            let uu____24069 = elim_delayed_subst_args args  in
            (uu____24066, uu____24069)  in
          FStar_Syntax_Syntax.Tm_app uu____24049  in
        mk1 uu____24048
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___352_24141 = p  in
              let uu____24142 =
                let uu____24143 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____24143  in
              {
                FStar_Syntax_Syntax.v = uu____24142;
                FStar_Syntax_Syntax.p =
                  (uu___352_24141.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___353_24145 = p  in
              let uu____24146 =
                let uu____24147 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____24147  in
              {
                FStar_Syntax_Syntax.v = uu____24146;
                FStar_Syntax_Syntax.p =
                  (uu___353_24145.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___354_24154 = p  in
              let uu____24155 =
                let uu____24156 =
                  let uu____24163 = elim_bv x  in
                  let uu____24164 = elim_delayed_subst_term t0  in
                  (uu____24163, uu____24164)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____24156  in
              {
                FStar_Syntax_Syntax.v = uu____24155;
                FStar_Syntax_Syntax.p =
                  (uu___354_24154.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___355_24187 = p  in
              let uu____24188 =
                let uu____24189 =
                  let uu____24202 =
                    FStar_List.map
                      (fun uu____24225  ->
                         match uu____24225 with
                         | (x,b) ->
                             let uu____24238 = elim_pat x  in
                             (uu____24238, b)) pats
                     in
                  (fv, uu____24202)  in
                FStar_Syntax_Syntax.Pat_cons uu____24189  in
              {
                FStar_Syntax_Syntax.v = uu____24188;
                FStar_Syntax_Syntax.p =
                  (uu___355_24187.FStar_Syntax_Syntax.p)
              }
          | uu____24251 -> p  in
        let elim_branch uu____24275 =
          match uu____24275 with
          | (pat,wopt,t3) ->
              let uu____24301 = elim_pat pat  in
              let uu____24304 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____24307 = elim_delayed_subst_term t3  in
              (uu____24301, uu____24304, uu____24307)
           in
        let uu____24312 =
          let uu____24313 =
            let uu____24336 = elim_delayed_subst_term t2  in
            let uu____24339 = FStar_List.map elim_branch branches  in
            (uu____24336, uu____24339)  in
          FStar_Syntax_Syntax.Tm_match uu____24313  in
        mk1 uu____24312
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____24470 =
          match uu____24470 with
          | (tc,topt) ->
              let uu____24505 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____24515 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____24515
                | FStar_Util.Inr c ->
                    let uu____24517 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____24517
                 in
              let uu____24518 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____24505, uu____24518)
           in
        let uu____24527 =
          let uu____24528 =
            let uu____24555 = elim_delayed_subst_term t2  in
            let uu____24558 = elim_ascription a  in
            (uu____24555, uu____24558, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____24528  in
        mk1 uu____24527
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___356_24619 = lb  in
          let uu____24620 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____24623 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___356_24619.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___356_24619.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____24620;
            FStar_Syntax_Syntax.lbeff =
              (uu___356_24619.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____24623;
            FStar_Syntax_Syntax.lbattrs =
              (uu___356_24619.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___356_24619.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____24626 =
          let uu____24627 =
            let uu____24640 =
              let uu____24647 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____24647)  in
            let uu____24656 = elim_delayed_subst_term t2  in
            (uu____24640, uu____24656)  in
          FStar_Syntax_Syntax.Tm_let uu____24627  in
        mk1 uu____24626
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____24700 =
          let uu____24701 =
            let uu____24708 = elim_delayed_subst_term tm  in
            (uu____24708, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____24701  in
        mk1 uu____24700
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____24719 =
          let uu____24720 =
            let uu____24727 = elim_delayed_subst_term t2  in
            let uu____24730 = elim_delayed_subst_meta md  in
            (uu____24727, uu____24730)  in
          FStar_Syntax_Syntax.Tm_meta uu____24720  in
        mk1 uu____24719

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___269_24739  ->
         match uu___269_24739 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____24743 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____24743
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
        let uu____24766 =
          let uu____24767 =
            let uu____24776 = elim_delayed_subst_term t  in
            (uu____24776, uopt)  in
          FStar_Syntax_Syntax.Total uu____24767  in
        mk1 uu____24766
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____24793 =
          let uu____24794 =
            let uu____24803 = elim_delayed_subst_term t  in
            (uu____24803, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____24794  in
        mk1 uu____24793
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___357_24812 = ct  in
          let uu____24813 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____24816 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____24827 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___357_24812.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___357_24812.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____24813;
            FStar_Syntax_Syntax.effect_args = uu____24816;
            FStar_Syntax_Syntax.flags = uu____24827
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___270_24830  ->
    match uu___270_24830 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____24844 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____24844
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____24883 =
          let uu____24890 = elim_delayed_subst_term t  in (m, uu____24890)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____24883
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____24902 =
          let uu____24911 = elim_delayed_subst_term t  in
          (m1, m2, uu____24911)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____24902
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
      (fun uu____24944  ->
         match uu____24944 with
         | (t,q) ->
             let uu____24963 = elim_delayed_subst_term t  in (uu____24963, q))
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
      (fun uu____24991  ->
         match uu____24991 with
         | (x,q) ->
             let uu____25010 =
               let uu___358_25011 = x  in
               let uu____25012 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___358_25011.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___358_25011.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____25012
               }  in
             (uu____25010, q)) bs

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
            | (uu____25118,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____25150,FStar_Util.Inl t) ->
                let uu____25172 =
                  let uu____25179 =
                    let uu____25180 =
                      let uu____25195 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____25195)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____25180  in
                  FStar_Syntax_Syntax.mk uu____25179  in
                uu____25172 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____25211 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____25211 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____25243 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____25316 ->
                    let uu____25317 =
                      let uu____25326 =
                        let uu____25327 = FStar_Syntax_Subst.compress t4  in
                        uu____25327.FStar_Syntax_Syntax.n  in
                      (uu____25326, tc)  in
                    (match uu____25317 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____25356) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____25403) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____25448,FStar_Util.Inl uu____25449) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____25480 -> failwith "Impossible")
                 in
              (match uu____25243 with
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
          let uu____25617 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____25617 with
          | (univ_names1,binders1,tc) ->
              let uu____25691 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____25691)
  
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
          let uu____25744 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____25744 with
          | (univ_names1,binders1,tc) ->
              let uu____25818 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____25818)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____25859 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____25859 with
           | (univ_names1,binders1,typ1) ->
               let uu___359_25899 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___359_25899.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___359_25899.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___359_25899.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___359_25899.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___360_25914 = s  in
          let uu____25915 =
            let uu____25916 =
              let uu____25925 = FStar_List.map (elim_uvars env) sigs  in
              (uu____25925, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____25916  in
          {
            FStar_Syntax_Syntax.sigel = uu____25915;
            FStar_Syntax_Syntax.sigrng =
              (uu___360_25914.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___360_25914.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___360_25914.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___360_25914.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____25942 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25942 with
           | (univ_names1,uu____25966,typ1) ->
               let uu___361_25988 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___361_25988.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___361_25988.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___361_25988.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___361_25988.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____25994 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____25994 with
           | (univ_names1,uu____26018,typ1) ->
               let uu___362_26040 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___362_26040.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___362_26040.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___362_26040.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___362_26040.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____26068 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____26068 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____26093 =
                            let uu____26094 =
                              let uu____26095 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____26095  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____26094
                             in
                          elim_delayed_subst_term uu____26093  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___363_26098 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___363_26098.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___363_26098.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___363_26098.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___363_26098.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___364_26099 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___364_26099.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___364_26099.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___364_26099.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___364_26099.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___365_26105 = s  in
          let uu____26106 =
            let uu____26107 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____26107  in
          {
            FStar_Syntax_Syntax.sigel = uu____26106;
            FStar_Syntax_Syntax.sigrng =
              (uu___365_26105.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___365_26105.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___365_26105.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___365_26105.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____26111 = elim_uvars_aux_t env us [] t  in
          (match uu____26111 with
           | (us1,uu____26135,t1) ->
               let uu___366_26157 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___366_26157.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___366_26157.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___366_26157.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___366_26157.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____26158 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____26160 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____26160 with
           | (univs1,binders,signature) ->
               let uu____26200 =
                 let uu____26205 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____26205 with
                 | (univs_opening,univs2) ->
                     let uu____26228 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____26228)
                  in
               (match uu____26200 with
                | (univs_opening,univs_closing) ->
                    let uu____26231 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____26237 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____26238 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____26237, uu____26238)  in
                    (match uu____26231 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____26264 =
                           match uu____26264 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____26282 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____26282 with
                                | (us1,t1) ->
                                    let uu____26293 =
                                      let uu____26302 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____26313 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____26302, uu____26313)  in
                                    (match uu____26293 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____26342 =
                                           let uu____26351 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____26362 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____26351, uu____26362)  in
                                         (match uu____26342 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____26392 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____26392
                                                 in
                                              let uu____26393 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____26393 with
                                               | (uu____26420,uu____26421,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____26444 =
                                                       let uu____26445 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____26445
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____26444
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____26454 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____26454 with
                           | (uu____26473,uu____26474,t1) -> t1  in
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
                             | uu____26550 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____26577 =
                               let uu____26578 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____26578.FStar_Syntax_Syntax.n  in
                             match uu____26577 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____26637 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____26670 =
                               let uu____26671 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____26671.FStar_Syntax_Syntax.n  in
                             match uu____26670 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____26694) ->
                                 let uu____26719 = destruct_action_body body
                                    in
                                 (match uu____26719 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____26768 ->
                                 let uu____26769 = destruct_action_body t  in
                                 (match uu____26769 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____26824 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____26824 with
                           | (action_univs,t) ->
                               let uu____26833 = destruct_action_typ_templ t
                                  in
                               (match uu____26833 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___367_26880 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___367_26880.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___367_26880.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___368_26882 = ed  in
                           let uu____26883 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____26884 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____26885 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____26886 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____26887 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____26888 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____26889 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____26890 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____26891 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____26892 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____26893 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____26894 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____26895 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____26896 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___368_26882.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___368_26882.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____26883;
                             FStar_Syntax_Syntax.bind_wp = uu____26884;
                             FStar_Syntax_Syntax.if_then_else = uu____26885;
                             FStar_Syntax_Syntax.ite_wp = uu____26886;
                             FStar_Syntax_Syntax.stronger = uu____26887;
                             FStar_Syntax_Syntax.close_wp = uu____26888;
                             FStar_Syntax_Syntax.assert_p = uu____26889;
                             FStar_Syntax_Syntax.assume_p = uu____26890;
                             FStar_Syntax_Syntax.null_wp = uu____26891;
                             FStar_Syntax_Syntax.trivial = uu____26892;
                             FStar_Syntax_Syntax.repr = uu____26893;
                             FStar_Syntax_Syntax.return_repr = uu____26894;
                             FStar_Syntax_Syntax.bind_repr = uu____26895;
                             FStar_Syntax_Syntax.actions = uu____26896;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___368_26882.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___369_26899 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___369_26899.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___369_26899.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___369_26899.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___369_26899.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___271_26920 =
            match uu___271_26920 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____26951 = elim_uvars_aux_t env us [] t  in
                (match uu____26951 with
                 | (us1,uu____26983,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___370_27014 = sub_eff  in
            let uu____27015 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____27018 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___370_27014.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___370_27014.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____27015;
              FStar_Syntax_Syntax.lift = uu____27018
            }  in
          let uu___371_27021 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___371_27021.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___371_27021.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___371_27021.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___371_27021.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____27031 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____27031 with
           | (univ_names1,binders1,comp1) ->
               let uu___372_27071 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___372_27071.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___372_27071.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___372_27071.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___372_27071.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____27074 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____27075 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      normalize
        [FStar_TypeChecker_Env.EraseUniverses;
        FStar_TypeChecker_Env.AllowUnboundUniverses] env t
  