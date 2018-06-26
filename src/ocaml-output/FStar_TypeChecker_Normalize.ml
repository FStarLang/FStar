open Prims
let cases :
  'Auu____11 'Auu____12 .
    ('Auu____11 -> 'Auu____12) ->
      'Auu____12 -> 'Auu____11 FStar_Pervasives_Native.option -> 'Auu____12
  =
  fun f  ->
    fun d  ->
      fun uu___239_32  ->
        match uu___239_32 with
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
    match uu____839 with | (hd1,uu____853) -> hd1
  
let mk :
  'Auu____876 .
    'Auu____876 ->
      FStar_Range.range -> 'Auu____876 FStar_Syntax_Syntax.syntax
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
          let uu____939 = FStar_ST.op_Bang r  in
          match uu____939 with
          | FStar_Pervasives_Native.Some uu____991 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,closure)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____1067 =
      FStar_List.map
        (fun uu____1081  ->
           match uu____1081 with
           | (bopt,c) ->
               let uu____1094 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____1096 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____1094 uu____1096) env
       in
    FStar_All.pipe_right uu____1067 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___240_1099  ->
    match uu___240_1099 with
    | Clos (env,t,uu____1102,uu____1103) ->
        let uu____1148 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____1155 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____1148 uu____1155
    | Univ uu____1156 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___241_1161  ->
    match uu___241_1161 with
    | Arg (c,uu____1163,uu____1164) ->
        let uu____1165 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____1165
    | MemoLazy uu____1166 -> "MemoLazy"
    | Abs (uu____1173,bs,uu____1175,uu____1176,uu____1177) ->
        let uu____1182 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____1182
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
  fun uu___242_1249  ->
    match uu___242_1249 with | [] -> true | uu____1252 -> false
  
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
                     failwith "Impossible: universe variable bound to a term"
               with
               | uu____1499 ->
                   if
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else failwith "Universe variable not found")
          | FStar_Syntax_Syntax.U_unif uu____1505 when
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1514 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1523 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1530 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____1530 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____1547 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____1547 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1555 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1563 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____1563 with
                                  | (uu____1568,m) -> n1 <= m))
                           in
                        if uu____1555 then rest1 else us1
                    | uu____1573 -> us1)
               | uu____1578 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1582 = aux u3  in
              FStar_List.map (fun _0_16  -> FStar_Syntax_Syntax.U_succ _0_16)
                uu____1582
           in
        if
          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1586 = aux u  in
           match uu____1586 with
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
            (fun uu____1734  ->
               let uu____1735 = FStar_Syntax_Print.tag_of_term t  in
               let uu____1736 = env_to_string env  in
               let uu____1737 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____1735 uu____1736 uu____1737);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____1746 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____1749 ->
                    let uu____1772 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____1772
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____1773 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____1774 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____1775 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____1776 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____1800 ->
                           let uu____1813 =
                             let uu____1814 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____1815 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____1814 uu____1815
                              in
                           failwith uu____1813
                       | uu____1818 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___243_1853  ->
                                         match uu___243_1853 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____1860 =
                                               let uu____1867 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____1867)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____1860
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___262_1877 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___262_1877.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___262_1877.FStar_Syntax_Syntax.sort)
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
                                              | uu____1882 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____1885 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___263_1889 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___263_1889.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___263_1889.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____1910 =
                        let uu____1911 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____1911  in
                      mk uu____1910 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____1919 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____1919  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____1921 = lookup_bvar env x  in
                    (match uu____1921 with
                     | Univ uu____1924 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___264_1928 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___264_1928.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___264_1928.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____1934,uu____1935) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____2020  ->
                              fun stack1  ->
                                match uu____2020 with
                                | (a,aq) ->
                                    let uu____2032 =
                                      let uu____2033 =
                                        let uu____2040 =
                                          let uu____2041 =
                                            let uu____2072 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____2072, false)  in
                                          Clos uu____2041  in
                                        (uu____2040, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____2033  in
                                    uu____2032 :: stack1) args)
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
                    let uu____2248 = close_binders cfg env bs  in
                    (match uu____2248 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____2295 =
                      let uu____2306 =
                        let uu____2313 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____2313]  in
                      close_binders cfg env uu____2306  in
                    (match uu____2295 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____2348 =
                             let uu____2349 =
                               let uu____2356 =
                                 let uu____2357 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____2357
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____2356, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____2349  in
                           mk uu____2348 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____2448 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____2448
                      | FStar_Util.Inr c ->
                          let uu____2462 = close_comp cfg env c  in
                          FStar_Util.Inr uu____2462
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____2481 =
                        let uu____2482 =
                          let uu____2509 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____2509, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____2482  in
                      mk uu____2481 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____2555 =
                            let uu____2556 =
                              let uu____2563 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____2563, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____2556  in
                          mk uu____2555 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____2615  -> dummy :: env1) env
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
                    let uu____2636 =
                      let uu____2647 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____2647
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____2666 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___265_2682 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___265_2682.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___265_2682.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____2666))
                       in
                    (match uu____2636 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___266_2700 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___266_2700.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___266_2700.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___266_2700.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___266_2700.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____2714,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____2777  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____2794 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____2794
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____2806  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____2830 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____2830
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___267_2838 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___267_2838.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___267_2838.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___268_2839 = lb  in
                      let uu____2840 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___268_2839.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___268_2839.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____2840;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___268_2839.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___268_2839.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____2872  -> fun env1  -> dummy :: env1)
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
            (fun uu____2961  ->
               let uu____2962 = FStar_Syntax_Print.tag_of_term t  in
               let uu____2963 = env_to_string env  in
               let uu____2964 = stack_to_string stack  in
               let uu____2965 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____2962 uu____2963 uu____2964 uu____2965);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____2970,uu____2971),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____3048 = close_binders cfg env' bs  in
               (match uu____3048 with
                | (bs1,uu____3062) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____3078 =
                      let uu___269_3081 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___269_3081.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___269_3081.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____3078)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____3137 =
                 match uu____3137 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____3252 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____3281 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____3365  ->
                                     fun uu____3366  ->
                                       match (uu____3365, uu____3366) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____3505 = norm_pat env4 p1
                                              in
                                           (match uu____3505 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____3281 with
                            | (pats1,env4) ->
                                ((let uu___270_3667 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___270_3667.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___271_3686 = x  in
                             let uu____3687 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___271_3686.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___271_3686.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3687
                             }  in
                           ((let uu___272_3701 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___272_3701.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___273_3712 = x  in
                             let uu____3713 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___273_3712.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___273_3712.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3713
                             }  in
                           ((let uu___274_3727 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___274_3727.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___275_3743 = x  in
                             let uu____3744 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___275_3743.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___275_3743.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3744
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___276_3761 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___276_3761.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____3766 = norm_pat env2 pat  in
                     (match uu____3766 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____3835 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____3835
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____3854 =
                   let uu____3855 =
                     let uu____3878 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____3878)  in
                   FStar_Syntax_Syntax.Tm_match uu____3855  in
                 mk uu____3854 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____3991 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____4080  ->
                                       match uu____4080 with
                                       | (a,q) ->
                                           let uu____4099 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____4099, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____3991
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____4110 =
                       let uu____4117 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____4117)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____4110
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____4129 =
                       let uu____4138 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____4138)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____4129
                 | uu____4143 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____4149 -> failwith "Impossible: unexpected stack element")

and (close_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
           FStar_Pervasives_Native.tuple2 Prims.list,env)
          FStar_Pervasives_Native.tuple2)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____4163 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4236  ->
                  fun uu____4237  ->
                    match (uu____4236, uu____4237) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___277_4355 = b  in
                          let uu____4356 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___277_4355.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___277_4355.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4356
                          }  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp) :: out))) (env, []))
           in
        match uu____4163 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____4473 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4486 = inline_closure_env cfg env [] t  in
                 let uu____4487 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____4486 uu____4487
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4500 = inline_closure_env cfg env [] t  in
                 let uu____4501 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4500 uu____4501
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____4545  ->
                           match uu____4545 with
                           | (a,q) ->
                               let uu____4558 =
                                 inline_closure_env cfg env [] a  in
                               (uu____4558, q)))
                    in
                 let flags1 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___244_4573  ->
                           match uu___244_4573 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4577 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____4577
                           | f -> f))
                    in
                 let uu____4581 =
                   let uu___278_4582 = c1  in
                   let uu____4583 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____4583;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___278_4582.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags1
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____4581)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_All.pipe_right flags1
      (FStar_List.filter
         (fun uu___245_4593  ->
            match uu___245_4593 with
            | FStar_Syntax_Syntax.DECREASES uu____4594 -> false
            | uu____4597 -> true))

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
                   (fun uu___246_4615  ->
                      match uu___246_4615 with
                      | FStar_Syntax_Syntax.DECREASES uu____4616 -> false
                      | uu____4619 -> true))
               in
            let rc1 =
              let uu___279_4621 = rc  in
              let uu____4622 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___279_4621.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____4622;
                FStar_Syntax_Syntax.residual_flags = flags1
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____4631 -> lopt

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
    let uu____4698 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____4698 with
    | FStar_Pervasives_Native.Some e -> FStar_Syntax_Embeddings.unembed e t
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____4750 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____4750) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____4812  ->
           fun subst1  ->
             match uu____4812 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____4853,uu____4854)) ->
                      let uu____4913 = b  in
                      (match uu____4913 with
                       | (bv,uu____4921) ->
                           let uu____4922 =
                             let uu____4923 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____4923  in
                           if uu____4922
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____4928 = unembed_binder term1  in
                              match uu____4928 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____4935 =
                                      let uu___280_4936 = bv  in
                                      let uu____4937 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___280_4936.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___280_4936.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____4937
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____4935
                                     in
                                  let b_for_x =
                                    let uu____4941 =
                                      let uu____4948 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____4948)
                                       in
                                    FStar_Syntax_Syntax.NT uu____4941  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___247_4962  ->
                                         match uu___247_4962 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____4963,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____4965;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____4966;_})
                                             ->
                                             let uu____4971 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____4971
                                         | uu____4972 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____4973 -> subst1)) env []
  
let reduce_primops :
  'Auu____4996 'Auu____4997 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____4996) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____4997 ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          if
            Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
          then tm
          else
            (let uu____5045 = FStar_Syntax_Util.head_and_args tm  in
             match uu____5045 with
             | (head1,args) ->
                 let uu____5084 =
                   let uu____5085 = FStar_Syntax_Util.un_uinst head1  in
                   uu____5085.FStar_Syntax_Syntax.n  in
                 (match uu____5084 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____5091 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                      (match uu____5091 with
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
                                (fun uu____5117  ->
                                   let uu____5118 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name
                                      in
                                   let uu____5119 =
                                     FStar_Util.string_of_int l  in
                                   let uu____5126 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____5118 uu____5119 uu____5126);
                              tm)
                           else
                             (let uu____5128 =
                                if l = prim_step.FStar_TypeChecker_Cfg.arity
                                then (args, [])
                                else
                                  FStar_List.splitAt
                                    prim_step.FStar_TypeChecker_Cfg.arity
                                    args
                                 in
                              match uu____5128 with
                              | (args_1,args_2) ->
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____5241  ->
                                        let uu____5242 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____5242);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____5245  ->
                                             if
                                               prim_step.FStar_TypeChecker_Cfg.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let uu____5247 =
                                      prim_step.FStar_TypeChecker_Cfg.interpretation
                                        psc args_1
                                       in
                                    match uu____5247 with
                                    | FStar_Pervasives_Native.None  ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5255  ->
                                              let uu____5256 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____5256);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5262  ->
                                              let uu____5263 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____5264 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____5263 uu____5264);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____5265 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____5269  ->
                                 let uu____5270 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____5270);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5274  ->
                            let uu____5275 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5275);
                       (match args with
                        | (a1,uu____5279)::[] ->
                            FStar_Syntax_Embeddings.embed
                              FStar_Syntax_Embeddings.e_range
                              tm.FStar_Syntax_Syntax.pos
                              a1.FStar_Syntax_Syntax.pos
                        | uu____5296 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5308  ->
                            let uu____5309 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5309);
                       (match args with
                        | (t,uu____5313)::(r,uu____5315)::[] ->
                            let uu____5342 =
                              FStar_Syntax_Embeddings.try_unembed
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____5342 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____5348 -> tm))
                  | uu____5357 -> tm))
  
let reduce_equality :
  'Auu____5368 'Auu____5369 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv,'Auu____5368) FStar_Pervasives_Native.tuple2
         FStar_Pervasives_Native.option,closure)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        'Auu____5369 ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun cfg  ->
    fun tm  ->
      reduce_primops
        (let uu___281_5415 = cfg  in
         {
           FStar_TypeChecker_Cfg.steps =
             (let uu___282_5418 = FStar_TypeChecker_Cfg.default_steps  in
              {
                FStar_TypeChecker_Cfg.beta =
                  (uu___282_5418.FStar_TypeChecker_Cfg.beta);
                FStar_TypeChecker_Cfg.iota =
                  (uu___282_5418.FStar_TypeChecker_Cfg.iota);
                FStar_TypeChecker_Cfg.zeta =
                  (uu___282_5418.FStar_TypeChecker_Cfg.zeta);
                FStar_TypeChecker_Cfg.weak =
                  (uu___282_5418.FStar_TypeChecker_Cfg.weak);
                FStar_TypeChecker_Cfg.hnf =
                  (uu___282_5418.FStar_TypeChecker_Cfg.hnf);
                FStar_TypeChecker_Cfg.primops = true;
                FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                  (uu___282_5418.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                FStar_TypeChecker_Cfg.unfold_until =
                  (uu___282_5418.FStar_TypeChecker_Cfg.unfold_until);
                FStar_TypeChecker_Cfg.unfold_only =
                  (uu___282_5418.FStar_TypeChecker_Cfg.unfold_only);
                FStar_TypeChecker_Cfg.unfold_fully =
                  (uu___282_5418.FStar_TypeChecker_Cfg.unfold_fully);
                FStar_TypeChecker_Cfg.unfold_attr =
                  (uu___282_5418.FStar_TypeChecker_Cfg.unfold_attr);
                FStar_TypeChecker_Cfg.unfold_tac =
                  (uu___282_5418.FStar_TypeChecker_Cfg.unfold_tac);
                FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                  (uu___282_5418.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                FStar_TypeChecker_Cfg.simplify =
                  (uu___282_5418.FStar_TypeChecker_Cfg.simplify);
                FStar_TypeChecker_Cfg.erase_universes =
                  (uu___282_5418.FStar_TypeChecker_Cfg.erase_universes);
                FStar_TypeChecker_Cfg.allow_unbound_universes =
                  (uu___282_5418.FStar_TypeChecker_Cfg.allow_unbound_universes);
                FStar_TypeChecker_Cfg.reify_ =
                  (uu___282_5418.FStar_TypeChecker_Cfg.reify_);
                FStar_TypeChecker_Cfg.compress_uvars =
                  (uu___282_5418.FStar_TypeChecker_Cfg.compress_uvars);
                FStar_TypeChecker_Cfg.no_full_norm =
                  (uu___282_5418.FStar_TypeChecker_Cfg.no_full_norm);
                FStar_TypeChecker_Cfg.check_no_uvars =
                  (uu___282_5418.FStar_TypeChecker_Cfg.check_no_uvars);
                FStar_TypeChecker_Cfg.unmeta =
                  (uu___282_5418.FStar_TypeChecker_Cfg.unmeta);
                FStar_TypeChecker_Cfg.unascribe =
                  (uu___282_5418.FStar_TypeChecker_Cfg.unascribe);
                FStar_TypeChecker_Cfg.in_full_norm_request =
                  (uu___282_5418.FStar_TypeChecker_Cfg.in_full_norm_request);
                FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                  (uu___282_5418.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                FStar_TypeChecker_Cfg.nbe_step =
                  (uu___282_5418.FStar_TypeChecker_Cfg.nbe_step)
              });
           FStar_TypeChecker_Cfg.tcenv =
             (uu___281_5415.FStar_TypeChecker_Cfg.tcenv);
           FStar_TypeChecker_Cfg.debug =
             (uu___281_5415.FStar_TypeChecker_Cfg.debug);
           FStar_TypeChecker_Cfg.delta_level =
             (uu___281_5415.FStar_TypeChecker_Cfg.delta_level);
           FStar_TypeChecker_Cfg.primitive_steps =
             FStar_TypeChecker_Cfg.equality_ops;
           FStar_TypeChecker_Cfg.strong =
             (uu___281_5415.FStar_TypeChecker_Cfg.strong);
           FStar_TypeChecker_Cfg.memoize_lazy =
             (uu___281_5415.FStar_TypeChecker_Cfg.memoize_lazy);
           FStar_TypeChecker_Cfg.normalize_pure_lets =
             (uu___281_5415.FStar_TypeChecker_Cfg.normalize_pure_lets);
           FStar_TypeChecker_Cfg.reifying =
             (uu___281_5415.FStar_TypeChecker_Cfg.reifying)
         }) tm
  
let is_norm_request :
  'Auu____5425 .
    FStar_Syntax_Syntax.term -> 'Auu____5425 Prims.list -> Prims.bool
  =
  fun hd1  ->
    fun args  ->
      let uu____5440 =
        let uu____5447 =
          let uu____5448 = FStar_Syntax_Util.un_uinst hd1  in
          uu____5448.FStar_Syntax_Syntax.n  in
        (uu____5447, args)  in
      match uu____5440 with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5454::uu____5455::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5459::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize
      | (FStar_Syntax_Syntax.Tm_fvar fv,steps::uu____5464::uu____5465::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm
      | uu____5468 -> false
  
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s  -> FStar_List.mem FStar_TypeChecker_Env.NBE s 
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___248_5490  ->
    match uu___248_5490 with
    | FStar_Syntax_Embeddings.Zeta  -> [FStar_TypeChecker_Env.Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [FStar_TypeChecker_Env.Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [FStar_TypeChecker_Env.Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [FStar_TypeChecker_Env.Weak]
    | FStar_Syntax_Embeddings.HNF  -> [FStar_TypeChecker_Env.HNF]
    | FStar_Syntax_Embeddings.Primops  -> [FStar_TypeChecker_Env.Primops]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____5496 =
          let uu____5499 =
            let uu____5500 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldOnly uu____5500  in
          [uu____5499]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____5496
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____5506 =
          let uu____5509 =
            let uu____5510 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldFully uu____5510  in
          [uu____5509]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____5506
    | FStar_Syntax_Embeddings.UnfoldAttr t ->
        [FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.UnfoldAttr t]
    | FStar_Syntax_Embeddings.NBE  -> [FStar_TypeChecker_Env.NBE]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  = fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____5533 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term,'Auu____5533)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____5584 =
            let uu____5589 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_Syntax_Embeddings.try_unembed uu____5589 s  in
          match uu____5584 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____5605 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____5605
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
        | uu____5631::(tm,uu____5633)::[] ->
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
        | (tm,uu____5662)::[] ->
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
        | (steps,uu____5683)::uu____5684::(tm,uu____5686)::[] ->
            let add_exclude s z =
              if FStar_List.contains z s
              then s
              else (FStar_TypeChecker_Env.Exclude z) :: s  in
            let uu____5727 =
              let uu____5732 = full_norm steps  in parse_steps uu____5732  in
            (match uu____5727 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = FStar_TypeChecker_Env.Beta :: s  in
                 let s2 = add_exclude s1 FStar_TypeChecker_Env.Zeta  in
                 let s3 = add_exclude s2 FStar_TypeChecker_Env.Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____5771 -> FStar_Pervasives_Native.None
  
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun s  ->
      fun tm  ->
        let delta_level =
          let uu____5802 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___249_5807  ->
                    match uu___249_5807 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____5808 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____5809 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____5812 -> true
                    | uu____5815 -> false))
             in
          if uu____5802
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta]  in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____5822  ->
             let uu____5823 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____5823);
        (let tm_norm =
           let uu____5825 =
             let uu____5840 = FStar_TypeChecker_Cfg.cfg_env cfg  in
             uu____5840.FStar_TypeChecker_Env.nbe  in
           uu____5825 s cfg.FStar_TypeChecker_Cfg.tcenv tm  in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____5844  ->
              let uu____5845 = FStar_Syntax_Print.term_to_string tm_norm  in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____5845);
         tm_norm)
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___250_5852  ->
    match uu___250_5852 with
    | (App
        (uu____5855,{
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reify );
                      FStar_Syntax_Syntax.pos = uu____5856;
                      FStar_Syntax_Syntax.vars = uu____5857;_},uu____5858,uu____5859))::uu____5860
        -> true
    | uu____5865 -> false
  
let firstn :
  'Auu____5874 .
    Prims.int ->
      'Auu____5874 Prims.list ->
        ('Auu____5874 Prims.list,'Auu____5874 Prims.list)
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
          (uu____5916,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____5917;
                        FStar_Syntax_Syntax.vars = uu____5918;_},uu____5919,uu____5920))::uu____5921
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____5926 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____5949) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____5959) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____5978  ->
                  match uu____5978 with
                  | (a,uu____5986) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____5992 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____6015 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____6016 -> false
    | FStar_Syntax_Syntax.Tm_type uu____6029 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____6030 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____6031 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____6032 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____6033 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____6034 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____6041 -> false
    | FStar_Syntax_Syntax.Tm_let uu____6048 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____6061 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____6078 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____6091 -> true
    | FStar_Syntax_Syntax.Tm_match uu____6098 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____6160  ->
                   match uu____6160 with
                   | (a,uu____6168) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____6175) ->
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
                     (fun uu____6297  ->
                        match uu____6297 with
                        | (a,uu____6305) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____6310,uu____6311,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____6317,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____6323 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____6330 -> false
            | FStar_Syntax_Syntax.Meta_named uu____6331 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____6337 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____6343 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_fully  -> true | uu____6349 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_reify  -> true | uu____6355 -> false
  
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
            let uu____6384 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
            match uu____6384 with
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
              (fun uu____6512  ->
                 fun uu____6513  ->
                   match (uu____6512, uu____6513) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____6573 =
            match uu____6573 with
            | (x,y,z) ->
                let uu____6583 = FStar_Util.string_of_bool x  in
                let uu____6584 = FStar_Util.string_of_bool y  in
                let uu____6585 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____6583 uu____6584
                  uu____6585
             in
          let res =
            match (qninfo,
                    ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only),
                    ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully),
                    ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr))
            with
            | uu____6631 when FStar_TypeChecker_Env.qninfo_is_action qninfo
                ->
                let b = should_reify1 cfg  in
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____6677  ->
                      let uu____6678 = FStar_Syntax_Print.fv_to_string fv  in
                      let uu____6679 = FStar_Util.string_of_bool b  in
                      FStar_Util.print2
                        "should_unfold: For DM4F action %s, should_reify = %s\n"
                        uu____6678 uu____6679);
                 if b then reif else no)
            | uu____6687 when
                let uu____6728 = FStar_TypeChecker_Cfg.find_prim_step cfg fv
                   in
                FStar_Option.isSome uu____6728 ->
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____6733  ->
                      FStar_Util.print_string
                        "should_unfold: primitive step, no\n");
                 no)
            | (FStar_Pervasives_Native.Some
               (FStar_Util.Inr
                ({
                   FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                     ((is_rec,uu____6735),uu____6736);
                   FStar_Syntax_Syntax.sigrng = uu____6737;
                   FStar_Syntax_Syntax.sigquals = qs;
                   FStar_Syntax_Syntax.sigmeta = uu____6739;
                   FStar_Syntax_Syntax.sigattrs = uu____6740;_},uu____6741),uu____6742),uu____6743,uu____6744,uu____6745)
                when
                FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect qs ->
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____6850  ->
                      FStar_Util.print_string
                        "should_unfold: masked effect, no\n");
                 no)
            | (uu____6851,uu____6852,uu____6853,uu____6854) when
                (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                  &&
                  (FStar_Util.for_some
                     (FStar_Syntax_Util.attr_eq
                        FStar_Syntax_Util.tac_opaque_attr) attrs)
                ->
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____6921  ->
                      FStar_Util.print_string
                        "should_unfold: masked effect, no\n");
                 no)
            | (FStar_Pervasives_Native.Some
               (FStar_Util.Inr
                ({
                   FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                     ((is_rec,uu____6923),uu____6924);
                   FStar_Syntax_Syntax.sigrng = uu____6925;
                   FStar_Syntax_Syntax.sigquals = qs;
                   FStar_Syntax_Syntax.sigmeta = uu____6927;
                   FStar_Syntax_Syntax.sigattrs = uu____6928;_},uu____6929),uu____6930),uu____6931,uu____6932,uu____6933)
                when
                is_rec &&
                  (Prims.op_Negation
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                ->
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7038  ->
                      FStar_Util.print_string
                        "should_unfold: recursive function without zeta, no\n");
                 no)
            | (uu____7039,FStar_Pervasives_Native.Some
               uu____7040,uu____7041,uu____7042) ->
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7110  ->
                      let uu____7111 = FStar_Syntax_Print.fv_to_string fv  in
                      FStar_Util.print1
                        "should_unfold: Reached a %s with selective unfolding\n"
                        uu____7111);
                 (let uu____7112 =
                    let uu____7121 =
                      match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                      with
                      | FStar_Pervasives_Native.None  -> no
                      | FStar_Pervasives_Native.Some lids ->
                          let uu____7141 =
                            FStar_Util.for_some
                              (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                             in
                          FStar_All.pipe_left yesno uu____7141
                       in
                    let uu____7148 =
                      let uu____7157 =
                        match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                        with
                        | FStar_Pervasives_Native.None  -> no
                        | FStar_Pervasives_Native.Some ats ->
                            let uu____7177 =
                              FStar_Util.for_some
                                (fun at  ->
                                   FStar_Util.for_some
                                     (FStar_Syntax_Util.attr_eq at) ats)
                                attrs
                               in
                            FStar_All.pipe_left yesno uu____7177
                         in
                      let uu____7186 =
                        let uu____7195 =
                          match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                          with
                          | FStar_Pervasives_Native.None  -> no
                          | FStar_Pervasives_Native.Some lids ->
                              let uu____7215 =
                                FStar_Util.for_some
                                  (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                 in
                              FStar_All.pipe_left fullyno uu____7215
                           in
                        [uu____7195]  in
                      uu____7157 :: uu____7186  in
                    uu____7121 :: uu____7148  in
                  comb_or uu____7112))
            | (uu____7246,uu____7247,FStar_Pervasives_Native.Some
               uu____7248,uu____7249) ->
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7317  ->
                      let uu____7318 = FStar_Syntax_Print.fv_to_string fv  in
                      FStar_Util.print1
                        "should_unfold: Reached a %s with selective unfolding\n"
                        uu____7318);
                 (let uu____7319 =
                    let uu____7328 =
                      match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                      with
                      | FStar_Pervasives_Native.None  -> no
                      | FStar_Pervasives_Native.Some lids ->
                          let uu____7348 =
                            FStar_Util.for_some
                              (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                             in
                          FStar_All.pipe_left yesno uu____7348
                       in
                    let uu____7355 =
                      let uu____7364 =
                        match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                        with
                        | FStar_Pervasives_Native.None  -> no
                        | FStar_Pervasives_Native.Some ats ->
                            let uu____7384 =
                              FStar_Util.for_some
                                (fun at  ->
                                   FStar_Util.for_some
                                     (FStar_Syntax_Util.attr_eq at) ats)
                                attrs
                               in
                            FStar_All.pipe_left yesno uu____7384
                         in
                      let uu____7393 =
                        let uu____7402 =
                          match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                          with
                          | FStar_Pervasives_Native.None  -> no
                          | FStar_Pervasives_Native.Some lids ->
                              let uu____7422 =
                                FStar_Util.for_some
                                  (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                 in
                              FStar_All.pipe_left fullyno uu____7422
                           in
                        [uu____7402]  in
                      uu____7364 :: uu____7393  in
                    uu____7328 :: uu____7355  in
                  comb_or uu____7319))
            | (uu____7453,uu____7454,uu____7455,FStar_Pervasives_Native.Some
               uu____7456) ->
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7524  ->
                      let uu____7525 = FStar_Syntax_Print.fv_to_string fv  in
                      FStar_Util.print1
                        "should_unfold: Reached a %s with selective unfolding\n"
                        uu____7525);
                 (let uu____7526 =
                    let uu____7535 =
                      match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                      with
                      | FStar_Pervasives_Native.None  -> no
                      | FStar_Pervasives_Native.Some lids ->
                          let uu____7555 =
                            FStar_Util.for_some
                              (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                             in
                          FStar_All.pipe_left yesno uu____7555
                       in
                    let uu____7562 =
                      let uu____7571 =
                        match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                        with
                        | FStar_Pervasives_Native.None  -> no
                        | FStar_Pervasives_Native.Some ats ->
                            let uu____7591 =
                              FStar_Util.for_some
                                (fun at  ->
                                   FStar_Util.for_some
                                     (FStar_Syntax_Util.attr_eq at) ats)
                                attrs
                               in
                            FStar_All.pipe_left yesno uu____7591
                         in
                      let uu____7600 =
                        let uu____7609 =
                          match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                          with
                          | FStar_Pervasives_Native.None  -> no
                          | FStar_Pervasives_Native.Some lids ->
                              let uu____7629 =
                                FStar_Util.for_some
                                  (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                 in
                              FStar_All.pipe_left fullyno uu____7629
                           in
                        [uu____7609]  in
                      uu____7571 :: uu____7600  in
                    uu____7535 :: uu____7562  in
                  comb_or uu____7526))
            | uu____7660 ->
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7706  ->
                      let uu____7707 = FStar_Syntax_Print.fv_to_string fv  in
                      let uu____7708 =
                        FStar_Syntax_Print.delta_depth_to_string
                          fv.FStar_Syntax_Syntax.fv_delta
                         in
                      let uu____7709 =
                        FStar_Common.string_of_list
                          FStar_TypeChecker_Env.string_of_delta_level
                          cfg.FStar_TypeChecker_Cfg.delta_level
                         in
                      FStar_Util.print3
                        "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                        uu____7707 uu____7708 uu____7709);
                 (let uu____7710 =
                    FStar_All.pipe_right
                      cfg.FStar_TypeChecker_Cfg.delta_level
                      (FStar_Util.for_some
                         (fun uu___251_7714  ->
                            match uu___251_7714 with
                            | FStar_TypeChecker_Env.UnfoldTacDelta  -> false
                            | FStar_TypeChecker_Env.NoDelta  -> false
                            | FStar_TypeChecker_Env.InliningDelta  -> true
                            | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                                true
                            | FStar_TypeChecker_Env.Unfold l ->
                                FStar_TypeChecker_Common.delta_depth_greater_than
                                  fv.FStar_Syntax_Syntax.fv_delta l))
                     in
                  FStar_All.pipe_left yesno uu____7710))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____7727  ->
               let uu____7728 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____7729 =
                 let uu____7730 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____7730  in
               let uu____7731 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____7728 uu____7729 uu____7731);
          (match res with
           | (false ,uu____7732,uu____7733) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____7734 ->
               let uu____7741 =
                 let uu____7742 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____7742
                  in
               FStar_All.pipe_left failwith uu____7741)
  
let decide_unfolding :
  'Auu____7759 'Auu____7760 .
    FStar_TypeChecker_Cfg.cfg ->
      'Auu____7759 ->
        stack_elt Prims.list ->
          'Auu____7760 ->
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
                    let uu___283_7829 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___284_7832 = cfg.FStar_TypeChecker_Cfg.steps
                            in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___284_7832.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___284_7832.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___284_7832.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___284_7832.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___284_7832.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___284_7832.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___284_7832.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___284_7832.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___284_7832.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___284_7832.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___284_7832.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___284_7832.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___284_7832.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___284_7832.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___284_7832.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___284_7832.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___284_7832.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___284_7832.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___284_7832.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___284_7832.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___284_7832.FStar_TypeChecker_Cfg.nbe_step)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___283_7829.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___283_7829.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___283_7829.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___283_7829.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___283_7829.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___283_7829.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___283_7829.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___283_7829.FStar_TypeChecker_Cfg.reifying)
                    }  in
                  let stack' = (Cfg cfg) :: stack  in
                  FStar_Pervasives_Native.Some (cfg', stack')
              | Should_unfold_reify  ->
                  let uu____7850 =
                    let uu____7857 = FStar_List.tl stack  in
                    (cfg, uu____7857)  in
                  FStar_Pervasives_Native.Some uu____7850
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____8159 ->
                   let uu____8182 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____8182
               | uu____8183 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____8191  ->
               let uu____8192 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____8193 = FStar_Syntax_Print.term_to_string t1  in
               let uu____8194 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____8201 =
                 let uu____8202 =
                   let uu____8205 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8205
                    in
                 stack_to_string uu____8202  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____8192 uu____8193 uu____8194 uu____8201);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8231  ->
                     let uu____8232 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8232);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____8233 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8237  ->
                     let uu____8238 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8238);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____8239 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8243  ->
                     let uu____8244 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8244);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____8245 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8249  ->
                     let uu____8250 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8250);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8251;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_17;
                 FStar_Syntax_Syntax.fv_qual = uu____8252;_}
               when _0_17 = (Prims.parse_int "0") ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8258  ->
                     let uu____8259 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8259);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8260;
                 FStar_Syntax_Syntax.fv_delta = uu____8261;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8265  ->
                     let uu____8266 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8266);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8267;
                 FStar_Syntax_Syntax.fv_delta = uu____8268;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____8269);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8279  ->
                     let uu____8280 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8280);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____8283 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv uu____8283
                  in
               let uu____8284 =
                 decide_unfolding cfg env stack t1.FStar_Syntax_Syntax.pos fv
                   qninfo
                  in
               (match uu____8284 with
                | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                    do_unfold_fv cfg1 env stack1 t1 qninfo fv
                | FStar_Pervasives_Native.None  -> rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_quoted uu____8311 ->
               let uu____8318 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____8318
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
                  && (is_norm_request hd1 args))
                 &&
                 (let uu____8348 =
                    FStar_Ident.lid_equals
                      (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____8348)
               ->
               (FStar_TypeChecker_Cfg.log_nbe cfg
                  (fun uu____8352  ->
                     let uu____8353 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "Reached norm_request for %s\n"
                       uu____8353);
                (let cfg' =
                   let uu___285_8355 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___286_8358 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___286_8358.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___286_8358.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___286_8358.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___286_8358.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___286_8358.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___286_8358.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___286_8358.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___286_8358.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___286_8358.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___286_8358.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___286_8358.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___286_8358.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___286_8358.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___286_8358.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___286_8358.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___286_8358.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___286_8358.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___286_8358.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___286_8358.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___286_8358.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___286_8358.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___286_8358.FStar_TypeChecker_Cfg.nbe_step)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___285_8355.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___285_8355.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___285_8355.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___285_8355.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___285_8355.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___285_8355.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____8363 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____8363 with
                 | FStar_Pervasives_Native.None  ->
                     let stack1 =
                       FStar_All.pipe_right stack
                         (FStar_List.fold_right
                            (fun uu____8392  ->
                               fun stack1  ->
                                 match uu____8392 with
                                 | (a,aq) ->
                                     let uu____8404 =
                                       let uu____8405 =
                                         let uu____8412 =
                                           let uu____8413 =
                                             let uu____8444 =
                                               FStar_Util.mk_ref
                                                 FStar_Pervasives_Native.None
                                                in
                                             (env, a, uu____8444, false)  in
                                           Clos uu____8413  in
                                         (uu____8412, aq,
                                           (t1.FStar_Syntax_Syntax.pos))
                                          in
                                       Arg uu____8405  in
                                     uu____8404 :: stack1) args)
                        in
                     (FStar_TypeChecker_Cfg.log cfg
                        (fun uu____8532  ->
                           let uu____8533 =
                             FStar_All.pipe_left FStar_Util.string_of_int
                               (FStar_List.length args)
                              in
                           FStar_Util.print1 "\tPushed %s arguments\n"
                             uu____8533);
                      norm cfg env stack1 hd1)
                 | FStar_Pervasives_Native.Some (s,tm) when is_nbe_request s
                     ->
                     let tm' = closure_as_term cfg env tm  in
                     let tm_norm = nbe_eval cfg s tm'  in
                     norm cfg env stack tm_norm
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     let delta_level =
                       let uu____8569 =
                         FStar_All.pipe_right s
                           (FStar_Util.for_some
                              (fun uu___252_8574  ->
                                 match uu___252_8574 with
                                 | FStar_TypeChecker_Env.UnfoldUntil
                                     uu____8575 -> true
                                 | FStar_TypeChecker_Env.UnfoldOnly
                                     uu____8576 -> true
                                 | FStar_TypeChecker_Env.UnfoldFully
                                     uu____8579 -> true
                                 | uu____8582 -> false))
                          in
                       if uu____8569
                       then
                         [FStar_TypeChecker_Env.Unfold
                            FStar_Syntax_Syntax.delta_constant]
                       else [FStar_TypeChecker_Env.NoDelta]  in
                     let cfg'1 =
                       let uu___287_8587 = cfg  in
                       let uu____8588 =
                         let uu___288_8589 =
                           FStar_TypeChecker_Cfg.to_fsteps s  in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___288_8589.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___288_8589.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___288_8589.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___288_8589.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___288_8589.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___288_8589.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___288_8589.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                           FStar_TypeChecker_Cfg.unfold_until =
                             (uu___288_8589.FStar_TypeChecker_Cfg.unfold_until);
                           FStar_TypeChecker_Cfg.unfold_only =
                             (uu___288_8589.FStar_TypeChecker_Cfg.unfold_only);
                           FStar_TypeChecker_Cfg.unfold_fully =
                             (uu___288_8589.FStar_TypeChecker_Cfg.unfold_fully);
                           FStar_TypeChecker_Cfg.unfold_attr =
                             (uu___288_8589.FStar_TypeChecker_Cfg.unfold_attr);
                           FStar_TypeChecker_Cfg.unfold_tac =
                             (uu___288_8589.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___288_8589.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___288_8589.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___288_8589.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___288_8589.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___288_8589.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___288_8589.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___288_8589.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___288_8589.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___288_8589.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___288_8589.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request = true;
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___288_8589.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___288_8589.FStar_TypeChecker_Cfg.nbe_step)
                         }  in
                       {
                         FStar_TypeChecker_Cfg.steps = uu____8588;
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___287_8587.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___287_8587.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level = delta_level;
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___287_8587.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___287_8587.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___287_8587.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                         FStar_TypeChecker_Cfg.reifying =
                           (uu___287_8587.FStar_TypeChecker_Cfg.reifying)
                       }  in
                     let stack' =
                       let tail1 = (Cfg cfg) :: stack  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         let uu____8594 =
                           let uu____8595 =
                             let uu____8600 = FStar_Util.now ()  in
                             (t1, uu____8600)  in
                           Debug uu____8595  in
                         uu____8594 :: tail1
                       else tail1  in
                     norm cfg'1 env stack' tm))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____8604 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____8604
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____8613 =
                      let uu____8620 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____8620, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____8613  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____8629 = lookup_bvar env x  in
               (match uu____8629 with
                | Univ uu____8630 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                    then
                      let uu____8679 = FStar_ST.op_Bang r  in
                      (match uu____8679 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____8801  ->
                                 let uu____8802 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____8803 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____8802
                                   uu____8803);
                            (let uu____8804 = maybe_weakly_reduced t'  in
                             if uu____8804
                             then
                               match stack with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____8805 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____8876)::uu____8877 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____8887,uu____8888))::stack_rest ->
                    (match c with
                     | Univ uu____8892 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____8901 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____8922  ->
                                    let uu____8923 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____8923);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____8951  ->
                                    let uu____8952 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____8952);
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
                       (fun uu____9018  ->
                          let uu____9019 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____9019);
                     norm cfg env stack1 t1)
                | (Match uu____9020)::uu____9021 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 =
                        if
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___289_9035 =
                               cfg.FStar_TypeChecker_Cfg.steps  in
                             {
                               FStar_TypeChecker_Cfg.beta =
                                 (uu___289_9035.FStar_TypeChecker_Cfg.beta);
                               FStar_TypeChecker_Cfg.iota = false;
                               FStar_TypeChecker_Cfg.zeta = false;
                               FStar_TypeChecker_Cfg.weak = false;
                               FStar_TypeChecker_Cfg.hnf =
                                 (uu___289_9035.FStar_TypeChecker_Cfg.hnf);
                               FStar_TypeChecker_Cfg.primops = false;
                               FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                 = true;
                               FStar_TypeChecker_Cfg.unfold_until =
                                 (uu___289_9035.FStar_TypeChecker_Cfg.unfold_until);
                               FStar_TypeChecker_Cfg.unfold_only =
                                 (uu___289_9035.FStar_TypeChecker_Cfg.unfold_only);
                               FStar_TypeChecker_Cfg.unfold_fully =
                                 (uu___289_9035.FStar_TypeChecker_Cfg.unfold_fully);
                               FStar_TypeChecker_Cfg.unfold_attr =
                                 (uu___289_9035.FStar_TypeChecker_Cfg.unfold_attr);
                               FStar_TypeChecker_Cfg.unfold_tac =
                                 (uu___289_9035.FStar_TypeChecker_Cfg.unfold_tac);
                               FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                 = false;
                               FStar_TypeChecker_Cfg.simplify = false;
                               FStar_TypeChecker_Cfg.erase_universes =
                                 (uu___289_9035.FStar_TypeChecker_Cfg.erase_universes);
                               FStar_TypeChecker_Cfg.allow_unbound_universes
                                 =
                                 (uu___289_9035.FStar_TypeChecker_Cfg.allow_unbound_universes);
                               FStar_TypeChecker_Cfg.reify_ = false;
                               FStar_TypeChecker_Cfg.compress_uvars =
                                 (uu___289_9035.FStar_TypeChecker_Cfg.compress_uvars);
                               FStar_TypeChecker_Cfg.no_full_norm = true;
                               FStar_TypeChecker_Cfg.check_no_uvars =
                                 (uu___289_9035.FStar_TypeChecker_Cfg.check_no_uvars);
                               FStar_TypeChecker_Cfg.unmeta = false;
                               FStar_TypeChecker_Cfg.unascribe = false;
                               FStar_TypeChecker_Cfg.in_full_norm_request =
                                 (uu___289_9035.FStar_TypeChecker_Cfg.in_full_norm_request);
                               FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                 =
                                 (uu___289_9035.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                               FStar_TypeChecker_Cfg.nbe_step =
                                 (uu___289_9035.FStar_TypeChecker_Cfg.nbe_step)
                             }  in
                           let cfg' =
                             let uu___290_9037 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps = steps';
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___290_9037.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___290_9037.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 [FStar_TypeChecker_Env.NoDelta];
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___290_9037.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong =
                                 (uu___290_9037.FStar_TypeChecker_Cfg.strong);
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___290_9037.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___290_9037.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___290_9037.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____9039 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9039 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9071  -> dummy :: env1) env)
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
                                          let uu____9112 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9112)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___291_9119 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___291_9119.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___291_9119.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9120 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9126  ->
                                 let uu____9127 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9127);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___292_9136 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___292_9136.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___292_9136.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___292_9136.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___292_9136.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___292_9136.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___292_9136.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___292_9136.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___292_9136.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____9139)::uu____9140 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 =
                        if
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___289_9150 =
                               cfg.FStar_TypeChecker_Cfg.steps  in
                             {
                               FStar_TypeChecker_Cfg.beta =
                                 (uu___289_9150.FStar_TypeChecker_Cfg.beta);
                               FStar_TypeChecker_Cfg.iota = false;
                               FStar_TypeChecker_Cfg.zeta = false;
                               FStar_TypeChecker_Cfg.weak = false;
                               FStar_TypeChecker_Cfg.hnf =
                                 (uu___289_9150.FStar_TypeChecker_Cfg.hnf);
                               FStar_TypeChecker_Cfg.primops = false;
                               FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                 = true;
                               FStar_TypeChecker_Cfg.unfold_until =
                                 (uu___289_9150.FStar_TypeChecker_Cfg.unfold_until);
                               FStar_TypeChecker_Cfg.unfold_only =
                                 (uu___289_9150.FStar_TypeChecker_Cfg.unfold_only);
                               FStar_TypeChecker_Cfg.unfold_fully =
                                 (uu___289_9150.FStar_TypeChecker_Cfg.unfold_fully);
                               FStar_TypeChecker_Cfg.unfold_attr =
                                 (uu___289_9150.FStar_TypeChecker_Cfg.unfold_attr);
                               FStar_TypeChecker_Cfg.unfold_tac =
                                 (uu___289_9150.FStar_TypeChecker_Cfg.unfold_tac);
                               FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                 = false;
                               FStar_TypeChecker_Cfg.simplify = false;
                               FStar_TypeChecker_Cfg.erase_universes =
                                 (uu___289_9150.FStar_TypeChecker_Cfg.erase_universes);
                               FStar_TypeChecker_Cfg.allow_unbound_universes
                                 =
                                 (uu___289_9150.FStar_TypeChecker_Cfg.allow_unbound_universes);
                               FStar_TypeChecker_Cfg.reify_ = false;
                               FStar_TypeChecker_Cfg.compress_uvars =
                                 (uu___289_9150.FStar_TypeChecker_Cfg.compress_uvars);
                               FStar_TypeChecker_Cfg.no_full_norm = true;
                               FStar_TypeChecker_Cfg.check_no_uvars =
                                 (uu___289_9150.FStar_TypeChecker_Cfg.check_no_uvars);
                               FStar_TypeChecker_Cfg.unmeta = false;
                               FStar_TypeChecker_Cfg.unascribe = false;
                               FStar_TypeChecker_Cfg.in_full_norm_request =
                                 (uu___289_9150.FStar_TypeChecker_Cfg.in_full_norm_request);
                               FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                 =
                                 (uu___289_9150.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                               FStar_TypeChecker_Cfg.nbe_step =
                                 (uu___289_9150.FStar_TypeChecker_Cfg.nbe_step)
                             }  in
                           let cfg' =
                             let uu___290_9152 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps = steps';
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___290_9152.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___290_9152.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 [FStar_TypeChecker_Env.NoDelta];
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___290_9152.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong =
                                 (uu___290_9152.FStar_TypeChecker_Cfg.strong);
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___290_9152.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___290_9152.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___290_9152.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____9154 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9154 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9186  -> dummy :: env1) env)
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
                                          let uu____9227 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9227)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___291_9234 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___291_9234.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___291_9234.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9235 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9241  ->
                                 let uu____9242 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9242);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___292_9251 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___292_9251.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___292_9251.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___292_9251.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___292_9251.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___292_9251.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___292_9251.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___292_9251.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___292_9251.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____9254)::uu____9255 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 =
                        if
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___289_9267 =
                               cfg.FStar_TypeChecker_Cfg.steps  in
                             {
                               FStar_TypeChecker_Cfg.beta =
                                 (uu___289_9267.FStar_TypeChecker_Cfg.beta);
                               FStar_TypeChecker_Cfg.iota = false;
                               FStar_TypeChecker_Cfg.zeta = false;
                               FStar_TypeChecker_Cfg.weak = false;
                               FStar_TypeChecker_Cfg.hnf =
                                 (uu___289_9267.FStar_TypeChecker_Cfg.hnf);
                               FStar_TypeChecker_Cfg.primops = false;
                               FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                 = true;
                               FStar_TypeChecker_Cfg.unfold_until =
                                 (uu___289_9267.FStar_TypeChecker_Cfg.unfold_until);
                               FStar_TypeChecker_Cfg.unfold_only =
                                 (uu___289_9267.FStar_TypeChecker_Cfg.unfold_only);
                               FStar_TypeChecker_Cfg.unfold_fully =
                                 (uu___289_9267.FStar_TypeChecker_Cfg.unfold_fully);
                               FStar_TypeChecker_Cfg.unfold_attr =
                                 (uu___289_9267.FStar_TypeChecker_Cfg.unfold_attr);
                               FStar_TypeChecker_Cfg.unfold_tac =
                                 (uu___289_9267.FStar_TypeChecker_Cfg.unfold_tac);
                               FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                 = false;
                               FStar_TypeChecker_Cfg.simplify = false;
                               FStar_TypeChecker_Cfg.erase_universes =
                                 (uu___289_9267.FStar_TypeChecker_Cfg.erase_universes);
                               FStar_TypeChecker_Cfg.allow_unbound_universes
                                 =
                                 (uu___289_9267.FStar_TypeChecker_Cfg.allow_unbound_universes);
                               FStar_TypeChecker_Cfg.reify_ = false;
                               FStar_TypeChecker_Cfg.compress_uvars =
                                 (uu___289_9267.FStar_TypeChecker_Cfg.compress_uvars);
                               FStar_TypeChecker_Cfg.no_full_norm = true;
                               FStar_TypeChecker_Cfg.check_no_uvars =
                                 (uu___289_9267.FStar_TypeChecker_Cfg.check_no_uvars);
                               FStar_TypeChecker_Cfg.unmeta = false;
                               FStar_TypeChecker_Cfg.unascribe = false;
                               FStar_TypeChecker_Cfg.in_full_norm_request =
                                 (uu___289_9267.FStar_TypeChecker_Cfg.in_full_norm_request);
                               FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                 =
                                 (uu___289_9267.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                               FStar_TypeChecker_Cfg.nbe_step =
                                 (uu___289_9267.FStar_TypeChecker_Cfg.nbe_step)
                             }  in
                           let cfg' =
                             let uu___290_9269 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps = steps';
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___290_9269.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___290_9269.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 [FStar_TypeChecker_Env.NoDelta];
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___290_9269.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong =
                                 (uu___290_9269.FStar_TypeChecker_Cfg.strong);
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___290_9269.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___290_9269.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___290_9269.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           norm cfg' env [] t1)
                         in
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
                                     fun uu____9303  -> dummy :: env1) env)
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
                                          let uu____9344 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9344)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___291_9351 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___291_9351.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___291_9351.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9352 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9358  ->
                                 let uu____9359 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9359);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___292_9368 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___292_9368.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___292_9368.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___292_9368.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___292_9368.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___292_9368.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___292_9368.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___292_9368.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___292_9368.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____9371)::uu____9372 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 =
                        if
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___289_9386 =
                               cfg.FStar_TypeChecker_Cfg.steps  in
                             {
                               FStar_TypeChecker_Cfg.beta =
                                 (uu___289_9386.FStar_TypeChecker_Cfg.beta);
                               FStar_TypeChecker_Cfg.iota = false;
                               FStar_TypeChecker_Cfg.zeta = false;
                               FStar_TypeChecker_Cfg.weak = false;
                               FStar_TypeChecker_Cfg.hnf =
                                 (uu___289_9386.FStar_TypeChecker_Cfg.hnf);
                               FStar_TypeChecker_Cfg.primops = false;
                               FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                 = true;
                               FStar_TypeChecker_Cfg.unfold_until =
                                 (uu___289_9386.FStar_TypeChecker_Cfg.unfold_until);
                               FStar_TypeChecker_Cfg.unfold_only =
                                 (uu___289_9386.FStar_TypeChecker_Cfg.unfold_only);
                               FStar_TypeChecker_Cfg.unfold_fully =
                                 (uu___289_9386.FStar_TypeChecker_Cfg.unfold_fully);
                               FStar_TypeChecker_Cfg.unfold_attr =
                                 (uu___289_9386.FStar_TypeChecker_Cfg.unfold_attr);
                               FStar_TypeChecker_Cfg.unfold_tac =
                                 (uu___289_9386.FStar_TypeChecker_Cfg.unfold_tac);
                               FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                 = false;
                               FStar_TypeChecker_Cfg.simplify = false;
                               FStar_TypeChecker_Cfg.erase_universes =
                                 (uu___289_9386.FStar_TypeChecker_Cfg.erase_universes);
                               FStar_TypeChecker_Cfg.allow_unbound_universes
                                 =
                                 (uu___289_9386.FStar_TypeChecker_Cfg.allow_unbound_universes);
                               FStar_TypeChecker_Cfg.reify_ = false;
                               FStar_TypeChecker_Cfg.compress_uvars =
                                 (uu___289_9386.FStar_TypeChecker_Cfg.compress_uvars);
                               FStar_TypeChecker_Cfg.no_full_norm = true;
                               FStar_TypeChecker_Cfg.check_no_uvars =
                                 (uu___289_9386.FStar_TypeChecker_Cfg.check_no_uvars);
                               FStar_TypeChecker_Cfg.unmeta = false;
                               FStar_TypeChecker_Cfg.unascribe = false;
                               FStar_TypeChecker_Cfg.in_full_norm_request =
                                 (uu___289_9386.FStar_TypeChecker_Cfg.in_full_norm_request);
                               FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                 =
                                 (uu___289_9386.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                               FStar_TypeChecker_Cfg.nbe_step =
                                 (uu___289_9386.FStar_TypeChecker_Cfg.nbe_step)
                             }  in
                           let cfg' =
                             let uu___290_9388 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps = steps';
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___290_9388.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___290_9388.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 [FStar_TypeChecker_Env.NoDelta];
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___290_9388.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong =
                                 (uu___290_9388.FStar_TypeChecker_Cfg.strong);
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___290_9388.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___290_9388.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___290_9388.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____9390 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9390 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9422  -> dummy :: env1) env)
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
                                          let uu____9463 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9463)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___291_9470 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___291_9470.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___291_9470.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9471 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9477  ->
                                 let uu____9478 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9478);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___292_9487 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___292_9487.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___292_9487.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___292_9487.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___292_9487.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___292_9487.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___292_9487.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___292_9487.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___292_9487.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____9490)::uu____9491 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 =
                        if
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___289_9505 =
                               cfg.FStar_TypeChecker_Cfg.steps  in
                             {
                               FStar_TypeChecker_Cfg.beta =
                                 (uu___289_9505.FStar_TypeChecker_Cfg.beta);
                               FStar_TypeChecker_Cfg.iota = false;
                               FStar_TypeChecker_Cfg.zeta = false;
                               FStar_TypeChecker_Cfg.weak = false;
                               FStar_TypeChecker_Cfg.hnf =
                                 (uu___289_9505.FStar_TypeChecker_Cfg.hnf);
                               FStar_TypeChecker_Cfg.primops = false;
                               FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                 = true;
                               FStar_TypeChecker_Cfg.unfold_until =
                                 (uu___289_9505.FStar_TypeChecker_Cfg.unfold_until);
                               FStar_TypeChecker_Cfg.unfold_only =
                                 (uu___289_9505.FStar_TypeChecker_Cfg.unfold_only);
                               FStar_TypeChecker_Cfg.unfold_fully =
                                 (uu___289_9505.FStar_TypeChecker_Cfg.unfold_fully);
                               FStar_TypeChecker_Cfg.unfold_attr =
                                 (uu___289_9505.FStar_TypeChecker_Cfg.unfold_attr);
                               FStar_TypeChecker_Cfg.unfold_tac =
                                 (uu___289_9505.FStar_TypeChecker_Cfg.unfold_tac);
                               FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                 = false;
                               FStar_TypeChecker_Cfg.simplify = false;
                               FStar_TypeChecker_Cfg.erase_universes =
                                 (uu___289_9505.FStar_TypeChecker_Cfg.erase_universes);
                               FStar_TypeChecker_Cfg.allow_unbound_universes
                                 =
                                 (uu___289_9505.FStar_TypeChecker_Cfg.allow_unbound_universes);
                               FStar_TypeChecker_Cfg.reify_ = false;
                               FStar_TypeChecker_Cfg.compress_uvars =
                                 (uu___289_9505.FStar_TypeChecker_Cfg.compress_uvars);
                               FStar_TypeChecker_Cfg.no_full_norm = true;
                               FStar_TypeChecker_Cfg.check_no_uvars =
                                 (uu___289_9505.FStar_TypeChecker_Cfg.check_no_uvars);
                               FStar_TypeChecker_Cfg.unmeta = false;
                               FStar_TypeChecker_Cfg.unascribe = false;
                               FStar_TypeChecker_Cfg.in_full_norm_request =
                                 (uu___289_9505.FStar_TypeChecker_Cfg.in_full_norm_request);
                               FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                 =
                                 (uu___289_9505.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                               FStar_TypeChecker_Cfg.nbe_step =
                                 (uu___289_9505.FStar_TypeChecker_Cfg.nbe_step)
                             }  in
                           let cfg' =
                             let uu___290_9507 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps = steps';
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___290_9507.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___290_9507.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 [FStar_TypeChecker_Env.NoDelta];
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___290_9507.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong =
                                 (uu___290_9507.FStar_TypeChecker_Cfg.strong);
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___290_9507.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___290_9507.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___290_9507.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           norm cfg' env [] t1)
                         in
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
                                     fun uu____9541  -> dummy :: env1) env)
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
                                          let uu____9582 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9582)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___291_9589 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___291_9589.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___291_9589.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9590 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9596  ->
                                 let uu____9597 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9597);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___292_9606 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___292_9606.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___292_9606.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___292_9606.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___292_9606.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___292_9606.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___292_9606.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___292_9606.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___292_9606.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____9609)::uu____9610 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 =
                        if
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___289_9628 =
                               cfg.FStar_TypeChecker_Cfg.steps  in
                             {
                               FStar_TypeChecker_Cfg.beta =
                                 (uu___289_9628.FStar_TypeChecker_Cfg.beta);
                               FStar_TypeChecker_Cfg.iota = false;
                               FStar_TypeChecker_Cfg.zeta = false;
                               FStar_TypeChecker_Cfg.weak = false;
                               FStar_TypeChecker_Cfg.hnf =
                                 (uu___289_9628.FStar_TypeChecker_Cfg.hnf);
                               FStar_TypeChecker_Cfg.primops = false;
                               FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                 = true;
                               FStar_TypeChecker_Cfg.unfold_until =
                                 (uu___289_9628.FStar_TypeChecker_Cfg.unfold_until);
                               FStar_TypeChecker_Cfg.unfold_only =
                                 (uu___289_9628.FStar_TypeChecker_Cfg.unfold_only);
                               FStar_TypeChecker_Cfg.unfold_fully =
                                 (uu___289_9628.FStar_TypeChecker_Cfg.unfold_fully);
                               FStar_TypeChecker_Cfg.unfold_attr =
                                 (uu___289_9628.FStar_TypeChecker_Cfg.unfold_attr);
                               FStar_TypeChecker_Cfg.unfold_tac =
                                 (uu___289_9628.FStar_TypeChecker_Cfg.unfold_tac);
                               FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                 = false;
                               FStar_TypeChecker_Cfg.simplify = false;
                               FStar_TypeChecker_Cfg.erase_universes =
                                 (uu___289_9628.FStar_TypeChecker_Cfg.erase_universes);
                               FStar_TypeChecker_Cfg.allow_unbound_universes
                                 =
                                 (uu___289_9628.FStar_TypeChecker_Cfg.allow_unbound_universes);
                               FStar_TypeChecker_Cfg.reify_ = false;
                               FStar_TypeChecker_Cfg.compress_uvars =
                                 (uu___289_9628.FStar_TypeChecker_Cfg.compress_uvars);
                               FStar_TypeChecker_Cfg.no_full_norm = true;
                               FStar_TypeChecker_Cfg.check_no_uvars =
                                 (uu___289_9628.FStar_TypeChecker_Cfg.check_no_uvars);
                               FStar_TypeChecker_Cfg.unmeta = false;
                               FStar_TypeChecker_Cfg.unascribe = false;
                               FStar_TypeChecker_Cfg.in_full_norm_request =
                                 (uu___289_9628.FStar_TypeChecker_Cfg.in_full_norm_request);
                               FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                 =
                                 (uu___289_9628.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                               FStar_TypeChecker_Cfg.nbe_step =
                                 (uu___289_9628.FStar_TypeChecker_Cfg.nbe_step)
                             }  in
                           let cfg' =
                             let uu___290_9630 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps = steps';
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___290_9630.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___290_9630.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 [FStar_TypeChecker_Env.NoDelta];
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___290_9630.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong =
                                 (uu___290_9630.FStar_TypeChecker_Cfg.strong);
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___290_9630.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___290_9630.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___290_9630.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____9632 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9632 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9664  -> dummy :: env1) env)
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
                                          let uu____9705 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9705)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___291_9712 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___291_9712.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___291_9712.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9713 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9719  ->
                                 let uu____9720 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9720);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___292_9729 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___292_9729.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___292_9729.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___292_9729.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___292_9729.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___292_9729.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___292_9729.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___292_9729.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___292_9729.FStar_TypeChecker_Cfg.reifying)
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
                      let t2 =
                        if
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___289_9735 =
                               cfg.FStar_TypeChecker_Cfg.steps  in
                             {
                               FStar_TypeChecker_Cfg.beta =
                                 (uu___289_9735.FStar_TypeChecker_Cfg.beta);
                               FStar_TypeChecker_Cfg.iota = false;
                               FStar_TypeChecker_Cfg.zeta = false;
                               FStar_TypeChecker_Cfg.weak = false;
                               FStar_TypeChecker_Cfg.hnf =
                                 (uu___289_9735.FStar_TypeChecker_Cfg.hnf);
                               FStar_TypeChecker_Cfg.primops = false;
                               FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                 = true;
                               FStar_TypeChecker_Cfg.unfold_until =
                                 (uu___289_9735.FStar_TypeChecker_Cfg.unfold_until);
                               FStar_TypeChecker_Cfg.unfold_only =
                                 (uu___289_9735.FStar_TypeChecker_Cfg.unfold_only);
                               FStar_TypeChecker_Cfg.unfold_fully =
                                 (uu___289_9735.FStar_TypeChecker_Cfg.unfold_fully);
                               FStar_TypeChecker_Cfg.unfold_attr =
                                 (uu___289_9735.FStar_TypeChecker_Cfg.unfold_attr);
                               FStar_TypeChecker_Cfg.unfold_tac =
                                 (uu___289_9735.FStar_TypeChecker_Cfg.unfold_tac);
                               FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                 = false;
                               FStar_TypeChecker_Cfg.simplify = false;
                               FStar_TypeChecker_Cfg.erase_universes =
                                 (uu___289_9735.FStar_TypeChecker_Cfg.erase_universes);
                               FStar_TypeChecker_Cfg.allow_unbound_universes
                                 =
                                 (uu___289_9735.FStar_TypeChecker_Cfg.allow_unbound_universes);
                               FStar_TypeChecker_Cfg.reify_ = false;
                               FStar_TypeChecker_Cfg.compress_uvars =
                                 (uu___289_9735.FStar_TypeChecker_Cfg.compress_uvars);
                               FStar_TypeChecker_Cfg.no_full_norm = true;
                               FStar_TypeChecker_Cfg.check_no_uvars =
                                 (uu___289_9735.FStar_TypeChecker_Cfg.check_no_uvars);
                               FStar_TypeChecker_Cfg.unmeta = false;
                               FStar_TypeChecker_Cfg.unascribe = false;
                               FStar_TypeChecker_Cfg.in_full_norm_request =
                                 (uu___289_9735.FStar_TypeChecker_Cfg.in_full_norm_request);
                               FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                 =
                                 (uu___289_9735.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                               FStar_TypeChecker_Cfg.nbe_step =
                                 (uu___289_9735.FStar_TypeChecker_Cfg.nbe_step)
                             }  in
                           let cfg' =
                             let uu___290_9737 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps = steps';
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___290_9737.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___290_9737.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 [FStar_TypeChecker_Env.NoDelta];
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___290_9737.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong =
                                 (uu___290_9737.FStar_TypeChecker_Cfg.strong);
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___290_9737.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___290_9737.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___290_9737.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____9739 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9739 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9771  -> dummy :: env1) env)
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
                                          let uu____9812 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9812)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___291_9819 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___291_9819.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___291_9819.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9820 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9826  ->
                                 let uu____9827 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9827);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___292_9836 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___292_9836.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___292_9836.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___292_9836.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___292_9836.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___292_9836.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___292_9836.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___292_9836.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___292_9836.FStar_TypeChecker_Cfg.reifying)
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
                      (fun uu____9875  ->
                         fun stack1  ->
                           match uu____9875 with
                           | (a,aq) ->
                               let uu____9887 =
                                 let uu____9888 =
                                   let uu____9895 =
                                     let uu____9896 =
                                       let uu____9927 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____9927, false)  in
                                     Clos uu____9896  in
                                   (uu____9895, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____9888  in
                               uu____9887 :: stack1) args)
                  in
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____10015  ->
                     let uu____10016 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____10016);
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
                             ((let uu___293_10062 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___293_10062.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___293_10062.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____10063 ->
                      let uu____10078 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10078)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____10081 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____10081 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____10106 =
                          let uu____10107 =
                            let uu____10114 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___294_10120 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___294_10120.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___294_10120.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____10114)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____10107  in
                        mk uu____10106 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____10139 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____10139
               else
                 (let uu____10141 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____10141 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____10149 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____10171  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____10149 c1  in
                      let t2 =
                        let uu____10193 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____10193 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____10304)::uu____10305 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10318  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____10319)::uu____10320 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10331  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____10332,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____10333;
                                   FStar_Syntax_Syntax.vars = uu____10334;_},uu____10335,uu____10336))::uu____10337
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10344  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____10345)::uu____10346 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10357  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____10358 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10361  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____10365  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____10390 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____10390
                         | FStar_Util.Inr c ->
                             let uu____10404 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____10404
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____10427 =
                               let uu____10428 =
                                 let uu____10455 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____10455, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____10428
                                in
                             mk uu____10427 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____10490 ->
                           let uu____10491 =
                             let uu____10492 =
                               let uu____10493 =
                                 let uu____10520 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____10520, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____10493
                                in
                             mk uu____10492 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____10491))))
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
                   let uu___295_10597 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___296_10600 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___296_10600.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___296_10600.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___296_10600.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___296_10600.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___296_10600.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___296_10600.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___296_10600.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___296_10600.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___296_10600.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___296_10600.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___296_10600.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___296_10600.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___296_10600.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___296_10600.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___296_10600.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___296_10600.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___296_10600.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___296_10600.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___296_10600.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___296_10600.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___296_10600.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___296_10600.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___296_10600.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___296_10600.FStar_TypeChecker_Cfg.nbe_step)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___295_10597.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___295_10597.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___295_10597.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___295_10597.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___295_10597.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___295_10597.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___295_10597.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___295_10597.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____10636 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____10636 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___297_10656 = cfg  in
                               let uu____10657 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___297_10656.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____10657;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___297_10656.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___297_10656.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___297_10656.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___297_10656.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___297_10656.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___297_10656.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___297_10656.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____10664 =
                                 let uu____10665 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____10665  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____10664
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___298_10668 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___298_10668.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___298_10668.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___298_10668.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___298_10668.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____10669 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____10669
           | FStar_Syntax_Syntax.Tm_let
               ((uu____10680,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____10681;
                               FStar_Syntax_Syntax.lbunivs = uu____10682;
                               FStar_Syntax_Syntax.lbtyp = uu____10683;
                               FStar_Syntax_Syntax.lbeff = uu____10684;
                               FStar_Syntax_Syntax.lbdef = uu____10685;
                               FStar_Syntax_Syntax.lbattrs = uu____10686;
                               FStar_Syntax_Syntax.lbpos = uu____10687;_}::uu____10688),uu____10689)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name
                   cfg.FStar_TypeChecker_Cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____10729 =
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
               if uu____10729
               then
                 let binder =
                   let uu____10731 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____10731  in
                 let env1 =
                   let uu____10741 =
                     let uu____10748 =
                       let uu____10749 =
                         let uu____10780 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____10780,
                           false)
                          in
                       Clos uu____10749  in
                     ((FStar_Pervasives_Native.Some binder), uu____10748)  in
                   uu____10741 :: env  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____10875  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                 then
                   (FStar_TypeChecker_Cfg.log cfg
                      (fun uu____10879  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____10880 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____10880))
                 else
                   (let uu____10882 =
                      let uu____10887 =
                        let uu____10888 =
                          let uu____10893 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____10893
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____10888]  in
                      FStar_Syntax_Subst.open_term uu____10887 body  in
                    match uu____10882 with
                    | (bs,body1) ->
                        (FStar_TypeChecker_Cfg.log cfg
                           (fun uu____10914  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____10922 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____10922  in
                            FStar_Util.Inl
                              (let uu___299_10932 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___299_10932.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___299_10932.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____10935  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___300_10937 = lb  in
                             let uu____10938 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___300_10937.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___300_10937.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____10938;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___300_10937.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___300_10937.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10963  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___301_10986 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps =
                                 (uu___301_10986.FStar_TypeChecker_Cfg.steps);
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___301_10986.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___301_10986.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 (uu___301_10986.FStar_TypeChecker_Cfg.delta_level);
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___301_10986.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong = true;
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___301_10986.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___301_10986.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___301_10986.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           FStar_TypeChecker_Cfg.log cfg1
                             (fun uu____10989  ->
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
               let uu____11006 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____11006 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____11042 =
                               let uu___302_11043 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___302_11043.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___302_11043.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____11042  in
                           let uu____11044 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____11044 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____11070 =
                                   FStar_List.map (fun uu____11086  -> dummy)
                                     lbs1
                                    in
                                 let uu____11087 =
                                   let uu____11096 =
                                     FStar_List.map
                                       (fun uu____11116  -> dummy) xs1
                                      in
                                   FStar_List.append uu____11096 env  in
                                 FStar_List.append uu____11070 uu____11087
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____11140 =
                                       let uu___303_11141 = rc  in
                                       let uu____11142 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___303_11141.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____11142;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___303_11141.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____11140
                                 | uu____11151 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___304_11157 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___304_11157.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___304_11157.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___304_11157.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___304_11157.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____11167 =
                        FStar_List.map (fun uu____11183  -> dummy) lbs2  in
                      FStar_List.append uu____11167 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____11191 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____11191 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___305_11207 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___305_11207.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___305_11207.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
               ->
               let uu____11236 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____11236
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____11255 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____11331  ->
                        match uu____11331 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___306_11452 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___306_11452.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___306_11452.FStar_Syntax_Syntax.sort)
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
               (match uu____11255 with
                | (rec_env,memos,uu____11679) ->
                    let uu____11732 =
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
                             let uu____12055 =
                               let uu____12062 =
                                 let uu____12063 =
                                   let uu____12094 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____12094, false)
                                    in
                                 Clos uu____12063  in
                               (FStar_Pervasives_Native.None, uu____12062)
                                in
                             uu____12055 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____12198  ->
                     let uu____12199 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____12199);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____12221 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____12223::uu____12224 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____12229) ->
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
                             | uu____12252 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____12266 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____12266
                              | uu____12277 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____12283 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____12307 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____12321 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____12334 =
                        let uu____12335 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____12336 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____12335 uu____12336
                         in
                      failwith uu____12334
                    else
                      (let uu____12338 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____12338)
                | uu____12339 -> norm cfg env stack t2))

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
              let uu____12348 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____12348 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____12362  ->
                        let uu____12363 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____12363);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____12374  ->
                        let uu____12375 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____12376 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____12375 uu____12376);
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
                      | (UnivArgs (us',uu____12389))::stack1 ->
                          ((let uu____12398 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____12398
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____12402 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____12402) us'
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
                      | uu____12435 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____12438 ->
                          let uu____12441 =
                            let uu____12442 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____12442
                             in
                          failwith uu____12441
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
                  let uu___307_12466 = cfg  in
                  let uu____12467 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____12467;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___307_12466.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___307_12466.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___307_12466.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___307_12466.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___307_12466.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___307_12466.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___307_12466.FStar_TypeChecker_Cfg.reifying)
                  }
                else
                  (let uu___308_12469 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___309_12472 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___309_12472.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___309_12472.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta = false;
                          FStar_TypeChecker_Cfg.weak =
                            (uu___309_12472.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___309_12472.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___309_12472.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___309_12472.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___309_12472.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___309_12472.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___309_12472.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___309_12472.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___309_12472.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___309_12472.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___309_12472.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___309_12472.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___309_12472.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___309_12472.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___309_12472.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___309_12472.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___309_12472.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___309_12472.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___309_12472.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___309_12472.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___309_12472.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___309_12472.FStar_TypeChecker_Cfg.nbe_step)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___308_12469.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___308_12469.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___308_12469.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___308_12469.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___308_12469.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___308_12469.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___308_12469.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___308_12469.FStar_TypeChecker_Cfg.reifying)
                   })
                 in
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
                  (fun uu____12506  ->
                     let uu____12507 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____12508 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____12507
                       uu____12508);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____12510 =
                   let uu____12511 = FStar_Syntax_Subst.compress head3  in
                   uu____12511.FStar_Syntax_Syntax.n  in
                 match uu____12510 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____12529 =
                         FStar_TypeChecker_Env.norm_eff_name
                           cfg.FStar_TypeChecker_Cfg.tcenv m
                          in
                       FStar_TypeChecker_Env.get_effect_decl
                         cfg.FStar_TypeChecker_Cfg.tcenv uu____12529
                        in
                     let uu____12530 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____12530 with
                      | (uu____12531,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____12541 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____12551 =
                                   let uu____12552 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____12552.FStar_Syntax_Syntax.n  in
                                 match uu____12551 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____12558,uu____12559))
                                     ->
                                     let uu____12568 =
                                       let uu____12569 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____12569.FStar_Syntax_Syntax.n  in
                                     (match uu____12568 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____12575,msrc,uu____12577))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____12586 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____12586
                                      | uu____12587 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____12588 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____12589 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____12589 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___310_12594 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___310_12594.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___310_12594.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___310_12594.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___310_12594.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___310_12594.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____12595 = FStar_List.tl stack  in
                                    let uu____12596 =
                                      let uu____12597 =
                                        let uu____12604 =
                                          let uu____12605 =
                                            let uu____12618 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____12618)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____12605
                                           in
                                        FStar_Syntax_Syntax.mk uu____12604
                                         in
                                      uu____12597
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____12595 uu____12596
                                | FStar_Pervasives_Native.None  ->
                                    let uu____12634 =
                                      let uu____12635 = is_return body  in
                                      match uu____12635 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____12639;
                                            FStar_Syntax_Syntax.vars =
                                              uu____12640;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____12643 -> false  in
                                    if uu____12634
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
                                         let uu____12664 =
                                           let uu____12671 =
                                             let uu____12672 =
                                               let uu____12689 =
                                                 let uu____12696 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____12696]  in
                                               (uu____12689, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____12672
                                              in
                                           FStar_Syntax_Syntax.mk uu____12671
                                            in
                                         uu____12664
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____12730 =
                                           let uu____12731 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____12731.FStar_Syntax_Syntax.n
                                            in
                                         match uu____12730 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____12737::uu____12738::[])
                                             ->
                                             let uu____12743 =
                                               let uu____12750 =
                                                 let uu____12751 =
                                                   let uu____12758 =
                                                     let uu____12759 =
                                                       let uu____12760 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.FStar_TypeChecker_Cfg.tcenv
                                                         uu____12760
                                                        in
                                                     let uu____12761 =
                                                       let uu____12764 =
                                                         let uu____12765 =
                                                           close1 t  in
                                                         (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.FStar_TypeChecker_Cfg.tcenv
                                                           uu____12765
                                                          in
                                                       [uu____12764]  in
                                                     uu____12759 ::
                                                       uu____12761
                                                      in
                                                   (bind1, uu____12758)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____12751
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____12750
                                                in
                                             uu____12743
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____12771 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____12783 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____12783
                                         then
                                           let uu____12792 =
                                             let uu____12799 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____12799
                                              in
                                           let uu____12800 =
                                             let uu____12809 =
                                               let uu____12816 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____12816
                                                in
                                             [uu____12809]  in
                                           uu____12792 :: uu____12800
                                         else []  in
                                       let reified =
                                         let uu____12845 =
                                           let uu____12852 =
                                             let uu____12853 =
                                               let uu____12868 =
                                                 let uu____12877 =
                                                   let uu____12886 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____12893 =
                                                     let uu____12902 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____12902]  in
                                                   uu____12886 :: uu____12893
                                                    in
                                                 let uu____12927 =
                                                   let uu____12936 =
                                                     let uu____12945 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____12952 =
                                                       let uu____12961 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____12968 =
                                                         let uu____12977 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____12984 =
                                                           let uu____12993 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____12993]  in
                                                         uu____12977 ::
                                                           uu____12984
                                                          in
                                                       uu____12961 ::
                                                         uu____12968
                                                        in
                                                     uu____12945 ::
                                                       uu____12952
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____12936
                                                    in
                                                 FStar_List.append
                                                   uu____12877 uu____12927
                                                  in
                                               (bind_inst, uu____12868)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____12853
                                              in
                                           FStar_Syntax_Syntax.mk uu____12852
                                            in
                                         uu____12845
                                           FStar_Pervasives_Native.None rng
                                          in
                                       FStar_TypeChecker_Cfg.log cfg
                                         (fun uu____13059  ->
                                            let uu____13060 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____13061 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____13060 uu____13061);
                                       (let uu____13062 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____13062 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____13086 =
                         FStar_TypeChecker_Env.norm_eff_name
                           cfg.FStar_TypeChecker_Cfg.tcenv m
                          in
                       FStar_TypeChecker_Env.get_effect_decl
                         cfg.FStar_TypeChecker_Cfg.tcenv uu____13086
                        in
                     let uu____13087 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____13087 with
                      | (uu____13088,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____13125 =
                                  let uu____13126 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____13126.FStar_Syntax_Syntax.n  in
                                match uu____13125 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____13130) -> t2
                                | uu____13135 -> head4  in
                              let uu____13136 =
                                let uu____13137 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____13137.FStar_Syntax_Syntax.n  in
                              match uu____13136 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____13143 -> FStar_Pervasives_Native.None
                               in
                            let uu____13144 = maybe_extract_fv head4  in
                            match uu____13144 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____13154 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv uu____13154
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____13159 = maybe_extract_fv head5
                                     in
                                  match uu____13159 with
                                  | FStar_Pervasives_Native.Some uu____13164
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____13165 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____13170 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____13185 =
                              match uu____13185 with
                              | (e,q) ->
                                  let uu____13192 =
                                    let uu____13193 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____13193.FStar_Syntax_Syntax.n  in
                                  (match uu____13192 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____13208 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____13208
                                   | uu____13209 -> false)
                               in
                            let uu____13210 =
                              let uu____13211 =
                                let uu____13220 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____13220 :: args  in
                              FStar_Util.for_some is_arg_impure uu____13211
                               in
                            if uu____13210
                            then
                              let uu____13239 =
                                let uu____13240 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____13240
                                 in
                              failwith uu____13239
                            else ());
                           (let uu____13242 = maybe_unfold_action head_app
                               in
                            match uu____13242 with
                            | (head_app1,found_action) ->
                                let mk1 tm =
                                  FStar_Syntax_Syntax.mk tm
                                    FStar_Pervasives_Native.None
                                    head3.FStar_Syntax_Syntax.pos
                                   in
                                let body =
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head_app1, args))
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
                                  | FStar_Pervasives_Native.Some (true ) ->
                                      body
                                   in
                                (FStar_TypeChecker_Cfg.log cfg
                                   (fun uu____13285  ->
                                      let uu____13286 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____13287 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____13286 uu____13287);
                                 (let uu____13288 = FStar_List.tl stack  in
                                  norm cfg env uu____13288 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____13290) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____13314 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____13314  in
                     (FStar_TypeChecker_Cfg.log cfg
                        (fun uu____13318  ->
                           let uu____13319 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____13319);
                      (let uu____13320 = FStar_List.tl stack  in
                       norm cfg env uu____13320 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____13441  ->
                               match uu____13441 with
                               | (pat,wopt,tm) ->
                                   let uu____13489 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____13489)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____13521 = FStar_List.tl stack  in
                     norm cfg env uu____13521 tm
                 | uu____13522 -> fallback ())

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
              (fun uu____13536  ->
                 let uu____13537 = FStar_Ident.string_of_lid msrc  in
                 let uu____13538 = FStar_Ident.string_of_lid mtgt  in
                 let uu____13539 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____13537
                   uu____13538 uu____13539);
            (let uu____13540 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____13540
             then
               let ed =
                 let uu____13542 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____13542  in
               let uu____13543 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____13543 with
               | (uu____13544,return_repr) ->
                   let return_inst =
                     let uu____13557 =
                       let uu____13558 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____13558.FStar_Syntax_Syntax.n  in
                     match uu____13557 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____13564::[]) ->
                         let uu____13569 =
                           let uu____13576 =
                             let uu____13577 =
                               let uu____13584 =
                                 let uu____13585 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____13585]  in
                               (return_tm, uu____13584)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____13577  in
                           FStar_Syntax_Syntax.mk uu____13576  in
                         uu____13569 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____13591 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____13594 =
                     let uu____13601 =
                       let uu____13602 =
                         let uu____13617 =
                           let uu____13626 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____13633 =
                             let uu____13642 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____13642]  in
                           uu____13626 :: uu____13633  in
                         (return_inst, uu____13617)  in
                       FStar_Syntax_Syntax.Tm_app uu____13602  in
                     FStar_Syntax_Syntax.mk uu____13601  in
                   uu____13594 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____13681 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____13681 with
                | FStar_Pervasives_Native.None  ->
                    let uu____13684 =
                      let uu____13685 = FStar_Ident.text_of_lid msrc  in
                      let uu____13686 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____13685 uu____13686
                       in
                    failwith uu____13684
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____13687;
                      FStar_TypeChecker_Env.mtarget = uu____13688;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____13689;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____13711 =
                      let uu____13712 = FStar_Ident.text_of_lid msrc  in
                      let uu____13713 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____13712 uu____13713
                       in
                    failwith uu____13711
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____13714;
                      FStar_TypeChecker_Env.mtarget = uu____13715;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____13716;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____13751 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____13752 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____13751 t FStar_Syntax_Syntax.tun uu____13752))

and (norm_pattern_args :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list Prims.list ->
        (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list Prims.list)
  =
  fun cfg  ->
    fun env  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____13808  ->
                   match uu____13808 with
                   | (a,imp) ->
                       let uu____13819 = norm cfg env [] a  in
                       (uu____13819, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____13827  ->
             let uu____13828 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____13829 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____13828 uu____13829);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____13853 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____13853
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___311_13856 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___311_13856.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___311_13856.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____13878 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____13878
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___312_13881 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___312_13881.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___312_13881.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____13918  ->
                      match uu____13918 with
                      | (a,i) ->
                          let uu____13929 = norm cfg env [] a  in
                          (uu____13929, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___253_13947  ->
                       match uu___253_13947 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____13951 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____13951
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___313_13959 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___314_13962 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___314_13962.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___313_13959.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___313_13959.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun uu____13965  ->
        match uu____13965 with
        | (x,imp) ->
            let uu____13968 =
              let uu___315_13969 = x  in
              let uu____13970 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___315_13969.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___315_13969.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____13970
              }  in
            (uu____13968, imp)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____13976 =
          FStar_List.fold_left
            (fun uu____14010  ->
               fun b  ->
                 match uu____14010 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____13976 with | (nbs,uu____14090) -> FStar_List.rev nbs

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
            let uu____14122 =
              let uu___316_14123 = rc  in
              let uu____14124 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___316_14123.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____14124;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___316_14123.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____14122
        | uu____14133 -> lopt

and (maybe_simplify :
  FStar_TypeChecker_Cfg.cfg ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,
      closure) FStar_Pervasives_Native.tuple2 Prims.list ->
      stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm  in
          if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.b380
          then
            (let uu____14154 = FStar_Syntax_Print.term_to_string tm  in
             let uu____14155 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____14154 uu____14155)
          else ();
          tm'

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
       FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option,
      closure) FStar_Pervasives_Native.tuple2 Prims.list ->
      stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 = reduce_primops cfg env stack tm  in
          let uu____14177 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____14177
          then tm1
          else
            (let w t =
               let uu___317_14191 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___317_14191.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___317_14191.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____14202 =
                 let uu____14203 = FStar_Syntax_Util.unmeta t  in
                 uu____14203.FStar_Syntax_Syntax.n  in
               match uu____14202 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____14210 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____14259)::args1,(bv,uu____14262)::bs1) ->
                   let uu____14296 =
                     let uu____14297 = FStar_Syntax_Subst.compress t  in
                     uu____14297.FStar_Syntax_Syntax.n  in
                   (match uu____14296 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____14301 -> false)
               | ([],[]) -> true
               | (uu____14322,uu____14323) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____14364 = FStar_Syntax_Print.term_to_string t  in
                  let uu____14365 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____14364
                    uu____14365)
               else ();
               (let uu____14367 = FStar_Syntax_Util.head_and_args' t  in
                match uu____14367 with
                | (hd1,args) ->
                    let uu____14400 =
                      let uu____14401 = FStar_Syntax_Subst.compress hd1  in
                      uu____14401.FStar_Syntax_Syntax.n  in
                    (match uu____14400 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____14408 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____14409 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____14410 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____14408 uu____14409 uu____14410)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____14412 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____14429 = FStar_Syntax_Print.term_to_string t  in
                  let uu____14430 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____14429
                    uu____14430)
               else ();
               (let uu____14432 = FStar_Syntax_Util.is_squash t  in
                match uu____14432 with
                | FStar_Pervasives_Native.Some (uu____14443,t') ->
                    is_applied bs t'
                | uu____14455 ->
                    let uu____14464 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____14464 with
                     | FStar_Pervasives_Native.Some (uu____14475,t') ->
                         is_applied bs t'
                     | uu____14487 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____14511 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____14511 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____14518)::(q,uu____14520)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____14548 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____14549 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____14548 uu____14549)
                    else ();
                    (let uu____14551 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____14551 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____14556 =
                           let uu____14557 = FStar_Syntax_Subst.compress p
                              in
                           uu____14557.FStar_Syntax_Syntax.n  in
                         (match uu____14556 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____14565 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____14565))
                          | uu____14568 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____14571)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____14588 =
                           let uu____14589 = FStar_Syntax_Subst.compress p1
                              in
                           uu____14589.FStar_Syntax_Syntax.n  in
                         (match uu____14588 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____14597 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____14597))
                          | uu____14600 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____14604 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____14604 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____14609 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____14609 with
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
                                     let uu____14620 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____14620))
                               | uu____14623 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____14628)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____14645 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____14645 with
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
                                     let uu____14656 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____14656))
                               | uu____14659 -> FStar_Pervasives_Native.None)
                          | uu____14662 -> FStar_Pervasives_Native.None)
                     | uu____14665 -> FStar_Pervasives_Native.None))
               | uu____14668 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____14681 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____14681 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____14687)::[],uu____14688,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____14699 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____14700 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____14699
                         uu____14700)
                    else ();
                    is_quantified_const bv phi')
               | uu____14702 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____14715 =
                 let uu____14716 = FStar_Syntax_Subst.compress phi  in
                 uu____14716.FStar_Syntax_Syntax.n  in
               match uu____14715 with
               | FStar_Syntax_Syntax.Tm_match (uu____14721,br::brs) ->
                   let uu____14788 = br  in
                   (match uu____14788 with
                    | (uu____14805,uu____14806,e) ->
                        let r =
                          let uu____14827 = simp_t e  in
                          match uu____14827 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____14833 =
                                FStar_List.for_all
                                  (fun uu____14851  ->
                                     match uu____14851 with
                                     | (uu____14864,uu____14865,e') ->
                                         let uu____14879 = simp_t e'  in
                                         uu____14879 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____14833
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____14887 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____14896 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____14896
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____14927 =
                 match uu____14927 with
                 | (t1,q) ->
                     let uu____14940 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____14940 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____14968 -> (t1, q))
                  in
               let uu____14979 = FStar_Syntax_Util.head_and_args t  in
               match uu____14979 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____15045 =
                 let uu____15046 = FStar_Syntax_Util.unmeta ty  in
                 uu____15046.FStar_Syntax_Syntax.n  in
               match uu____15045 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____15050) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____15055,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____15075 -> false  in
             let simplify1 arg =
               let uu____15100 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____15100, arg)  in
             let uu____15109 = is_forall_const tm1  in
             match uu____15109 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____15114 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____15115 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____15114
                       uu____15115)
                  else ();
                  (let uu____15117 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____15117))
             | FStar_Pervasives_Native.None  ->
                 let uu____15118 =
                   let uu____15119 = FStar_Syntax_Subst.compress tm1  in
                   uu____15119.FStar_Syntax_Syntax.n  in
                 (match uu____15118 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____15123;
                              FStar_Syntax_Syntax.vars = uu____15124;_},uu____15125);
                         FStar_Syntax_Syntax.pos = uu____15126;
                         FStar_Syntax_Syntax.vars = uu____15127;_},args)
                      ->
                      let uu____15153 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____15153
                      then
                        let uu____15154 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____15154 with
                         | (FStar_Pervasives_Native.Some (true ),uu____15199)::
                             (uu____15200,(arg,uu____15202))::[] ->
                             maybe_auto_squash arg
                         | (uu____15251,(arg,uu____15253))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____15254)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____15303)::uu____15304::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____15355::(FStar_Pervasives_Native.Some (false
                                         ),uu____15356)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____15407 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____15421 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____15421
                         then
                           let uu____15422 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____15422 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____15467)::uu____15468::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____15519::(FStar_Pervasives_Native.Some (true
                                           ),uu____15520)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____15571)::(uu____15572,(arg,uu____15574))::[]
                               -> maybe_auto_squash arg
                           | (uu____15623,(arg,uu____15625))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____15626)::[]
                               -> maybe_auto_squash arg
                           | uu____15675 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____15689 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____15689
                            then
                              let uu____15690 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____15690 with
                              | uu____15735::(FStar_Pervasives_Native.Some
                                              (true ),uu____15736)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____15787)::uu____15788::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____15839)::(uu____15840,(arg,uu____15842))::[]
                                  -> maybe_auto_squash arg
                              | (uu____15891,(p,uu____15893))::(uu____15894,
                                                                (q,uu____15896))::[]
                                  ->
                                  let uu____15943 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____15943
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____15945 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____15959 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____15959
                               then
                                 let uu____15960 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____15960 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16005)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____16006)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____16057)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____16058)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16109)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____16110)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____16161)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____16162)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____16213,(arg,uu____16215))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____16216)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16265)::(uu____16266,(arg,uu____16268))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____16317,(arg,uu____16319))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____16320)::[]
                                     ->
                                     let uu____16369 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____16369
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____16370)::(uu____16371,(arg,uu____16373))::[]
                                     ->
                                     let uu____16422 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____16422
                                 | (uu____16423,(p,uu____16425))::(uu____16426,
                                                                   (q,uu____16428))::[]
                                     ->
                                     let uu____16475 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____16475
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____16477 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____16491 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____16491
                                  then
                                    let uu____16492 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____16492 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____16537)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____16568)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____16599 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____16613 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____16613
                                     then
                                       match args with
                                       | (t,uu____16615)::[] ->
                                           let uu____16632 =
                                             let uu____16633 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____16633.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____16632 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____16636::[],body,uu____16638)
                                                ->
                                                let uu____16665 = simp_t body
                                                   in
                                                (match uu____16665 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____16668 -> tm1)
                                            | uu____16671 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____16673))::(t,uu____16675)::[]
                                           ->
                                           let uu____16702 =
                                             let uu____16703 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____16703.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____16702 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____16706::[],body,uu____16708)
                                                ->
                                                let uu____16735 = simp_t body
                                                   in
                                                (match uu____16735 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____16738 -> tm1)
                                            | uu____16741 -> tm1)
                                       | uu____16742 -> tm1
                                     else
                                       (let uu____16752 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____16752
                                        then
                                          match args with
                                          | (t,uu____16754)::[] ->
                                              let uu____16771 =
                                                let uu____16772 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____16772.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____16771 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____16775::[],body,uu____16777)
                                                   ->
                                                   let uu____16804 =
                                                     simp_t body  in
                                                   (match uu____16804 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____16807 -> tm1)
                                               | uu____16810 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____16812))::(t,uu____16814)::[]
                                              ->
                                              let uu____16841 =
                                                let uu____16842 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____16842.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____16841 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____16845::[],body,uu____16847)
                                                   ->
                                                   let uu____16874 =
                                                     simp_t body  in
                                                   (match uu____16874 with
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
                                                    | uu____16877 -> tm1)
                                               | uu____16880 -> tm1)
                                          | uu____16881 -> tm1
                                        else
                                          (let uu____16891 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____16891
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____16892;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____16893;_},uu____16894)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____16911;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____16912;_},uu____16913)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____16930 -> tm1
                                           else
                                             (let uu____16940 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____16940 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____16960 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____16970;
                         FStar_Syntax_Syntax.vars = uu____16971;_},args)
                      ->
                      let uu____16993 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____16993
                      then
                        let uu____16994 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____16994 with
                         | (FStar_Pervasives_Native.Some (true ),uu____17039)::
                             (uu____17040,(arg,uu____17042))::[] ->
                             maybe_auto_squash arg
                         | (uu____17091,(arg,uu____17093))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____17094)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____17143)::uu____17144::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____17195::(FStar_Pervasives_Native.Some (false
                                         ),uu____17196)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____17247 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____17261 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____17261
                         then
                           let uu____17262 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____17262 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____17307)::uu____17308::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____17359::(FStar_Pervasives_Native.Some (true
                                           ),uu____17360)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____17411)::(uu____17412,(arg,uu____17414))::[]
                               -> maybe_auto_squash arg
                           | (uu____17463,(arg,uu____17465))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____17466)::[]
                               -> maybe_auto_squash arg
                           | uu____17515 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____17529 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____17529
                            then
                              let uu____17530 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____17530 with
                              | uu____17575::(FStar_Pervasives_Native.Some
                                              (true ),uu____17576)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____17627)::uu____17628::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____17679)::(uu____17680,(arg,uu____17682))::[]
                                  -> maybe_auto_squash arg
                              | (uu____17731,(p,uu____17733))::(uu____17734,
                                                                (q,uu____17736))::[]
                                  ->
                                  let uu____17783 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____17783
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____17785 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____17799 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____17799
                               then
                                 let uu____17800 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____17800 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17845)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17846)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17897)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____17898)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17949)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____17950)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18001)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18002)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____18053,(arg,uu____18055))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____18056)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18105)::(uu____18106,(arg,uu____18108))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____18157,(arg,uu____18159))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____18160)::[]
                                     ->
                                     let uu____18209 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____18209
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18210)::(uu____18211,(arg,uu____18213))::[]
                                     ->
                                     let uu____18262 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____18262
                                 | (uu____18263,(p,uu____18265))::(uu____18266,
                                                                   (q,uu____18268))::[]
                                     ->
                                     let uu____18315 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____18315
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____18317 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____18331 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____18331
                                  then
                                    let uu____18332 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____18332 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____18377)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____18408)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____18439 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____18453 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____18453
                                     then
                                       match args with
                                       | (t,uu____18455)::[] ->
                                           let uu____18472 =
                                             let uu____18473 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____18473.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____18472 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____18476::[],body,uu____18478)
                                                ->
                                                let uu____18505 = simp_t body
                                                   in
                                                (match uu____18505 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____18508 -> tm1)
                                            | uu____18511 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____18513))::(t,uu____18515)::[]
                                           ->
                                           let uu____18542 =
                                             let uu____18543 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____18543.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____18542 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____18546::[],body,uu____18548)
                                                ->
                                                let uu____18575 = simp_t body
                                                   in
                                                (match uu____18575 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____18578 -> tm1)
                                            | uu____18581 -> tm1)
                                       | uu____18582 -> tm1
                                     else
                                       (let uu____18592 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____18592
                                        then
                                          match args with
                                          | (t,uu____18594)::[] ->
                                              let uu____18611 =
                                                let uu____18612 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____18612.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____18611 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____18615::[],body,uu____18617)
                                                   ->
                                                   let uu____18644 =
                                                     simp_t body  in
                                                   (match uu____18644 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____18647 -> tm1)
                                               | uu____18650 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____18652))::(t,uu____18654)::[]
                                              ->
                                              let uu____18681 =
                                                let uu____18682 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____18682.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____18681 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____18685::[],body,uu____18687)
                                                   ->
                                                   let uu____18714 =
                                                     simp_t body  in
                                                   (match uu____18714 with
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
                                                    | uu____18717 -> tm1)
                                               | uu____18720 -> tm1)
                                          | uu____18721 -> tm1
                                        else
                                          (let uu____18731 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____18731
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18732;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18733;_},uu____18734)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18751;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18752;_},uu____18753)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____18770 -> tm1
                                           else
                                             (let uu____18780 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____18780 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____18800 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____18815 = simp_t t  in
                      (match uu____18815 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____18818 ->
                      let uu____18841 = is_const_match tm1  in
                      (match uu____18841 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____18844 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____18854  ->
               (let uu____18856 = FStar_Syntax_Print.tag_of_term t  in
                let uu____18857 = FStar_Syntax_Print.term_to_string t  in
                let uu____18858 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____18865 =
                  let uu____18866 =
                    let uu____18869 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____18869
                     in
                  stack_to_string uu____18866  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____18856 uu____18857 uu____18858 uu____18865);
               (let uu____18892 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____18892
                then
                  let uu____18893 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____18893 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____18900 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____18901 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____18902 =
                          let uu____18903 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____18903
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____18900
                          uu____18901 uu____18902);
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
                   let uu____18921 =
                     let uu____18922 =
                       let uu____18923 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____18923  in
                     FStar_Util.string_of_int uu____18922  in
                   let uu____18928 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____18929 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____18921 uu____18928 uu____18929)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____18935,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                FStar_TypeChecker_Cfg.log cfg
                  (fun uu____18986  ->
                     let uu____18987 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____18987);
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
               let uu____19025 =
                 let uu___318_19026 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___318_19026.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___318_19026.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____19025
           | (Arg (Univ uu____19029,uu____19030,uu____19031))::uu____19032 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____19035,uu____19036))::uu____19037 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____19052,uu____19053),aq,r))::stack1
               when
               let uu____19103 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____19103 ->
               let t2 =
                 let uu____19107 =
                   let uu____19112 =
                     let uu____19113 = closure_as_term cfg env_arg tm  in
                     (uu____19113, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____19112  in
                 uu____19107 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____19123),aq,r))::stack1 ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____19176  ->
                     let uu____19177 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____19177);
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
                  (let uu____19189 = FStar_ST.op_Bang m  in
                   match uu____19189 with
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
                   | FStar_Pervasives_Native.Some (uu____19332,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____19385 =
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____19389  ->
                      let uu____19390 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____19390);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____19396 =
                 let uu____19397 = FStar_Syntax_Subst.compress t1  in
                 uu____19397.FStar_Syntax_Syntax.n  in
               (match uu____19396 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____19424 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____19424  in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____19428  ->
                          let uu____19429 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____19429);
                     (let uu____19430 = FStar_List.tl stack  in
                      norm cfg env1 uu____19430 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____19431);
                       FStar_Syntax_Syntax.pos = uu____19432;
                       FStar_Syntax_Syntax.vars = uu____19433;_},(e,uu____19435)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____19464 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                    ->
                    let uu____19479 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____19479 with
                     | (hd1,args) ->
                         let uu____19516 =
                           let uu____19517 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____19517.FStar_Syntax_Syntax.n  in
                         (match uu____19516 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____19521 =
                                FStar_TypeChecker_Cfg.find_prim_step cfg fv
                                 in
                              (match uu____19521 with
                               | FStar_Pervasives_Native.Some
                                   {
                                     FStar_TypeChecker_Cfg.name = uu____19524;
                                     FStar_TypeChecker_Cfg.arity =
                                       uu____19525;
                                     FStar_TypeChecker_Cfg.auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     FStar_TypeChecker_Cfg.strong_reduction_ok
                                       = uu____19527;
                                     FStar_TypeChecker_Cfg.requires_binder_substitution
                                       = uu____19528;
                                     FStar_TypeChecker_Cfg.interpretation =
                                       uu____19529;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____19544 -> fallback " (3)" ())
                          | uu____19547 -> fallback " (4)" ()))
                | uu____19548 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (FStar_TypeChecker_Cfg.log cfg1
                  (fun uu____19571  ->
                     let uu____19572 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____19572);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____19581 =
                   FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____19586  ->
                        let uu____19587 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____19588 =
                          let uu____19589 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____19616  ->
                                    match uu____19616 with
                                    | (p,uu____19626,uu____19627) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____19589
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____19587 uu____19588);
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
                             (fun uu___254_19644  ->
                                match uu___254_19644 with
                                | FStar_TypeChecker_Env.InliningDelta  ->
                                    true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____19645 -> false))
                         in
                      let steps =
                        let uu___319_19647 = cfg1.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___319_19647.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___319_19647.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta = false;
                          FStar_TypeChecker_Cfg.weak =
                            (uu___319_19647.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___319_19647.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___319_19647.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___319_19647.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___319_19647.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_tac = false;
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___319_19647.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___319_19647.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___319_19647.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___319_19647.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___319_19647.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___319_19647.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___319_19647.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___319_19647.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___319_19647.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___319_19647.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___319_19647.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___319_19647.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___319_19647.FStar_TypeChecker_Cfg.nbe_step)
                        }  in
                      let uu___320_19652 = cfg1  in
                      {
                        FStar_TypeChecker_Cfg.steps = steps;
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___320_19652.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___320_19652.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level = new_delta;
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___320_19652.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong = true;
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___320_19652.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___320_19652.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying =
                          (uu___320_19652.FStar_TypeChecker_Cfg.reifying)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____19724 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____19753 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____19837  ->
                                    fun uu____19838  ->
                                      match (uu____19837, uu____19838) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____19977 = norm_pat env3 p1
                                             in
                                          (match uu____19977 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____19753 with
                           | (pats1,env3) ->
                               ((let uu___321_20139 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___321_20139.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___322_20158 = x  in
                            let uu____20159 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___322_20158.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___322_20158.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20159
                            }  in
                          ((let uu___323_20173 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___323_20173.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___324_20184 = x  in
                            let uu____20185 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___324_20184.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___324_20184.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20185
                            }  in
                          ((let uu___325_20199 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___325_20199.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___326_20215 = x  in
                            let uu____20216 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___326_20215.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___326_20215.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20216
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___327_20231 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___327_20231.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____20275 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____20305 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____20305 with
                                  | (p,wopt,e) ->
                                      let uu____20325 = norm_pat env1 p  in
                                      (match uu____20325 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____20380 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____20380
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____20397 =
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
                      if uu____20397
                      then
                        norm
                          (let uu___328_20402 = cfg1  in
                           {
                             FStar_TypeChecker_Cfg.steps =
                               (let uu___329_20405 =
                                  cfg1.FStar_TypeChecker_Cfg.steps  in
                                {
                                  FStar_TypeChecker_Cfg.beta =
                                    (uu___329_20405.FStar_TypeChecker_Cfg.beta);
                                  FStar_TypeChecker_Cfg.iota =
                                    (uu___329_20405.FStar_TypeChecker_Cfg.iota);
                                  FStar_TypeChecker_Cfg.zeta =
                                    (uu___329_20405.FStar_TypeChecker_Cfg.zeta);
                                  FStar_TypeChecker_Cfg.weak =
                                    (uu___329_20405.FStar_TypeChecker_Cfg.weak);
                                  FStar_TypeChecker_Cfg.hnf =
                                    (uu___329_20405.FStar_TypeChecker_Cfg.hnf);
                                  FStar_TypeChecker_Cfg.primops =
                                    (uu___329_20405.FStar_TypeChecker_Cfg.primops);
                                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                    =
                                    (uu___329_20405.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                  FStar_TypeChecker_Cfg.unfold_until =
                                    (uu___329_20405.FStar_TypeChecker_Cfg.unfold_until);
                                  FStar_TypeChecker_Cfg.unfold_only =
                                    (uu___329_20405.FStar_TypeChecker_Cfg.unfold_only);
                                  FStar_TypeChecker_Cfg.unfold_fully =
                                    (uu___329_20405.FStar_TypeChecker_Cfg.unfold_fully);
                                  FStar_TypeChecker_Cfg.unfold_attr =
                                    (uu___329_20405.FStar_TypeChecker_Cfg.unfold_attr);
                                  FStar_TypeChecker_Cfg.unfold_tac =
                                    (uu___329_20405.FStar_TypeChecker_Cfg.unfold_tac);
                                  FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                    =
                                    (uu___329_20405.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                  FStar_TypeChecker_Cfg.simplify =
                                    (uu___329_20405.FStar_TypeChecker_Cfg.simplify);
                                  FStar_TypeChecker_Cfg.erase_universes =
                                    (uu___329_20405.FStar_TypeChecker_Cfg.erase_universes);
                                  FStar_TypeChecker_Cfg.allow_unbound_universes
                                    =
                                    (uu___329_20405.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                  FStar_TypeChecker_Cfg.reify_ =
                                    (uu___329_20405.FStar_TypeChecker_Cfg.reify_);
                                  FStar_TypeChecker_Cfg.compress_uvars =
                                    (uu___329_20405.FStar_TypeChecker_Cfg.compress_uvars);
                                  FStar_TypeChecker_Cfg.no_full_norm =
                                    (uu___329_20405.FStar_TypeChecker_Cfg.no_full_norm);
                                  FStar_TypeChecker_Cfg.check_no_uvars =
                                    (uu___329_20405.FStar_TypeChecker_Cfg.check_no_uvars);
                                  FStar_TypeChecker_Cfg.unmeta =
                                    (uu___329_20405.FStar_TypeChecker_Cfg.unmeta);
                                  FStar_TypeChecker_Cfg.unascribe =
                                    (uu___329_20405.FStar_TypeChecker_Cfg.unascribe);
                                  FStar_TypeChecker_Cfg.in_full_norm_request
                                    =
                                    (uu___329_20405.FStar_TypeChecker_Cfg.in_full_norm_request);
                                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                    = false;
                                  FStar_TypeChecker_Cfg.nbe_step =
                                    (uu___329_20405.FStar_TypeChecker_Cfg.nbe_step)
                                });
                             FStar_TypeChecker_Cfg.tcenv =
                               (uu___328_20402.FStar_TypeChecker_Cfg.tcenv);
                             FStar_TypeChecker_Cfg.debug =
                               (uu___328_20402.FStar_TypeChecker_Cfg.debug);
                             FStar_TypeChecker_Cfg.delta_level =
                               (uu___328_20402.FStar_TypeChecker_Cfg.delta_level);
                             FStar_TypeChecker_Cfg.primitive_steps =
                               (uu___328_20402.FStar_TypeChecker_Cfg.primitive_steps);
                             FStar_TypeChecker_Cfg.strong =
                               (uu___328_20402.FStar_TypeChecker_Cfg.strong);
                             FStar_TypeChecker_Cfg.memoize_lazy =
                               (uu___328_20402.FStar_TypeChecker_Cfg.memoize_lazy);
                             FStar_TypeChecker_Cfg.normalize_pure_lets =
                               (uu___328_20402.FStar_TypeChecker_Cfg.normalize_pure_lets);
                             FStar_TypeChecker_Cfg.reifying =
                               (uu___328_20402.FStar_TypeChecker_Cfg.reifying)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____20407 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____20407)
                    in
                 let rec is_cons head1 =
                   let uu____20432 =
                     let uu____20433 = FStar_Syntax_Subst.compress head1  in
                     uu____20433.FStar_Syntax_Syntax.n  in
                   match uu____20432 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____20437) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____20442 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____20443;
                         FStar_Syntax_Syntax.fv_delta = uu____20444;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____20445;
                         FStar_Syntax_Syntax.fv_delta = uu____20446;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____20447);_}
                       -> true
                   | uu____20454 -> false  in
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
                   let uu____20617 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____20617 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____20704 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____20743 ->
                                 let uu____20744 =
                                   let uu____20745 = is_cons head1  in
                                   Prims.op_Negation uu____20745  in
                                 FStar_Util.Inr uu____20744)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____20770 =
                              let uu____20771 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____20771.FStar_Syntax_Syntax.n  in
                            (match uu____20770 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____20789 ->
                                 let uu____20790 =
                                   let uu____20791 = is_cons head1  in
                                   Prims.op_Negation uu____20791  in
                                 FStar_Util.Inr uu____20790))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____20868)::rest_a,(p1,uu____20871)::rest_p) ->
                       let uu____20915 = matches_pat t2 p1  in
                       (match uu____20915 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____20964 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____21082 = matches_pat scrutinee1 p1  in
                       (match uu____21082 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (FStar_TypeChecker_Cfg.log cfg1
                               (fun uu____21122  ->
                                  let uu____21123 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____21124 =
                                    let uu____21125 =
                                      FStar_List.map
                                        (fun uu____21135  ->
                                           match uu____21135 with
                                           | (uu____21140,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____21125
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____21123 uu____21124);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____21172  ->
                                       match uu____21172 with
                                       | (bv,t2) ->
                                           let uu____21195 =
                                             let uu____21202 =
                                               let uu____21205 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____21205
                                                in
                                             let uu____21206 =
                                               let uu____21207 =
                                                 let uu____21238 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____21238, false)
                                                  in
                                               Clos uu____21207  in
                                             (uu____21202, uu____21206)  in
                                           uu____21195 :: env2) env1 s
                                 in
                              let uu____21351 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____21351)))
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
          if is_nbe_request s then nbe_eval c s t else norm c [] [] t
  
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
        let uu____21415 = FStar_TypeChecker_Cfg.config s e  in
        norm_comp uu____21415 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____21432 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____21432 [] u
  
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
        let uu____21456 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____21456  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____21463 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___330_21482 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___330_21482.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___330_21482.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name
              cfg.FStar_TypeChecker_Cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____21489 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____21489
          then
            let ct1 =
              let uu____21491 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____21491 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____21498 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____21498
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___331_21502 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___331_21502.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___331_21502.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___331_21502.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev
                      cfg.FStar_TypeChecker_Cfg.tcenv c
                     in
                  let uu___332_21504 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___332_21504.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___332_21504.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___332_21504.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___332_21504.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___333_21505 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___333_21505.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___333_21505.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____21507 -> c
  
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
        let uu____21525 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____21525  in
      let uu____21532 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____21532
      then
        let uu____21533 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____21533 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____21539  ->
                 let uu____21540 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____21540)
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
            ((let uu____21561 =
                let uu____21566 =
                  let uu____21567 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____21567
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____21566)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____21561);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____21582 =
            FStar_TypeChecker_Cfg.config
              [FStar_TypeChecker_Env.AllowUnboundUniverses] env
             in
          norm_comp uu____21582 [] c
        with
        | e ->
            ((let uu____21595 =
                let uu____21600 =
                  let uu____21601 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____21601
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____21600)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____21595);
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
                   let uu____21646 =
                     let uu____21647 =
                       let uu____21654 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____21654)  in
                     FStar_Syntax_Syntax.Tm_refine uu____21647  in
                   mk uu____21646 t01.FStar_Syntax_Syntax.pos
               | uu____21659 -> t2)
          | uu____21660 -> t2  in
        aux t
  
let (unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      normalize
        [FStar_TypeChecker_Env.Primops;
        FStar_TypeChecker_Env.Weak;
        FStar_TypeChecker_Env.HNF;
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.Beta] env t
  
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
        let uu____21724 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____21724 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____21753 ->
                 let uu____21760 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____21760 with
                  | (actuals,uu____21770,uu____21771) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____21785 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____21785 with
                         | (binders,args) ->
                             let uu____21796 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____21796
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
      | uu____21810 ->
          let uu____21811 = FStar_Syntax_Util.head_and_args t  in
          (match uu____21811 with
           | (head1,args) ->
               let uu____21848 =
                 let uu____21849 = FStar_Syntax_Subst.compress head1  in
                 uu____21849.FStar_Syntax_Syntax.n  in
               (match uu____21848 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____21870 =
                      let uu____21883 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____21883  in
                    (match uu____21870 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____21913 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___338_21921 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___338_21921.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___338_21921.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___338_21921.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___338_21921.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___338_21921.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___338_21921.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___338_21921.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___338_21921.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___338_21921.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___338_21921.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___338_21921.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___338_21921.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___338_21921.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___338_21921.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___338_21921.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___338_21921.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___338_21921.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___338_21921.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___338_21921.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___338_21921.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___338_21921.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___338_21921.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___338_21921.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___338_21921.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___338_21921.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___338_21921.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___338_21921.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___338_21921.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___338_21921.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___338_21921.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___338_21921.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___338_21921.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___338_21921.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___338_21921.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___338_21921.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___338_21921.FStar_TypeChecker_Env.dep_graph);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___338_21921.FStar_TypeChecker_Env.nbe)
                                 }) t
                               in
                            match uu____21913 with
                            | (uu____21922,ty,uu____21924) ->
                                eta_expand_with_type env t ty))
                | uu____21925 ->
                    let uu____21926 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___339_21934 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___339_21934.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___339_21934.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___339_21934.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___339_21934.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___339_21934.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___339_21934.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___339_21934.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___339_21934.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___339_21934.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___339_21934.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___339_21934.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___339_21934.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___339_21934.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___339_21934.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___339_21934.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___339_21934.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___339_21934.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___339_21934.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___339_21934.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___339_21934.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___339_21934.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___339_21934.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___339_21934.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___339_21934.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___339_21934.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___339_21934.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___339_21934.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___339_21934.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___339_21934.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___339_21934.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___339_21934.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___339_21934.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___339_21934.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___339_21934.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___339_21934.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___339_21934.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___339_21934.FStar_TypeChecker_Env.nbe)
                         }) t
                       in
                    (match uu____21926 with
                     | (uu____21935,ty,uu____21937) ->
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
      let uu___340_22010 = x  in
      let uu____22011 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___340_22010.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___340_22010.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____22011
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____22014 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____22037 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____22038 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____22039 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____22040 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____22047 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____22048 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____22049 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___341_22079 = rc  in
          let uu____22080 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____22089 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___341_22079.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____22080;
            FStar_Syntax_Syntax.residual_flags = uu____22089
          }  in
        let uu____22092 =
          let uu____22093 =
            let uu____22110 = elim_delayed_subst_binders bs  in
            let uu____22117 = elim_delayed_subst_term t2  in
            let uu____22120 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____22110, uu____22117, uu____22120)  in
          FStar_Syntax_Syntax.Tm_abs uu____22093  in
        mk1 uu____22092
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____22151 =
          let uu____22152 =
            let uu____22165 = elim_delayed_subst_binders bs  in
            let uu____22172 = elim_delayed_subst_comp c  in
            (uu____22165, uu____22172)  in
          FStar_Syntax_Syntax.Tm_arrow uu____22152  in
        mk1 uu____22151
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____22189 =
          let uu____22190 =
            let uu____22197 = elim_bv bv  in
            let uu____22198 = elim_delayed_subst_term phi  in
            (uu____22197, uu____22198)  in
          FStar_Syntax_Syntax.Tm_refine uu____22190  in
        mk1 uu____22189
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____22225 =
          let uu____22226 =
            let uu____22241 = elim_delayed_subst_term t2  in
            let uu____22244 = elim_delayed_subst_args args  in
            (uu____22241, uu____22244)  in
          FStar_Syntax_Syntax.Tm_app uu____22226  in
        mk1 uu____22225
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___342_22312 = p  in
              let uu____22313 =
                let uu____22314 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____22314  in
              {
                FStar_Syntax_Syntax.v = uu____22313;
                FStar_Syntax_Syntax.p =
                  (uu___342_22312.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___343_22316 = p  in
              let uu____22317 =
                let uu____22318 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____22318  in
              {
                FStar_Syntax_Syntax.v = uu____22317;
                FStar_Syntax_Syntax.p =
                  (uu___343_22316.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___344_22325 = p  in
              let uu____22326 =
                let uu____22327 =
                  let uu____22334 = elim_bv x  in
                  let uu____22335 = elim_delayed_subst_term t0  in
                  (uu____22334, uu____22335)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____22327  in
              {
                FStar_Syntax_Syntax.v = uu____22326;
                FStar_Syntax_Syntax.p =
                  (uu___344_22325.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___345_22358 = p  in
              let uu____22359 =
                let uu____22360 =
                  let uu____22373 =
                    FStar_List.map
                      (fun uu____22396  ->
                         match uu____22396 with
                         | (x,b) ->
                             let uu____22409 = elim_pat x  in
                             (uu____22409, b)) pats
                     in
                  (fv, uu____22373)  in
                FStar_Syntax_Syntax.Pat_cons uu____22360  in
              {
                FStar_Syntax_Syntax.v = uu____22359;
                FStar_Syntax_Syntax.p =
                  (uu___345_22358.FStar_Syntax_Syntax.p)
              }
          | uu____22422 -> p  in
        let elim_branch uu____22446 =
          match uu____22446 with
          | (pat,wopt,t3) ->
              let uu____22472 = elim_pat pat  in
              let uu____22475 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____22478 = elim_delayed_subst_term t3  in
              (uu____22472, uu____22475, uu____22478)
           in
        let uu____22483 =
          let uu____22484 =
            let uu____22507 = elim_delayed_subst_term t2  in
            let uu____22510 = FStar_List.map elim_branch branches  in
            (uu____22507, uu____22510)  in
          FStar_Syntax_Syntax.Tm_match uu____22484  in
        mk1 uu____22483
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____22641 =
          match uu____22641 with
          | (tc,topt) ->
              let uu____22676 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____22686 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____22686
                | FStar_Util.Inr c ->
                    let uu____22688 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____22688
                 in
              let uu____22689 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____22676, uu____22689)
           in
        let uu____22698 =
          let uu____22699 =
            let uu____22726 = elim_delayed_subst_term t2  in
            let uu____22729 = elim_ascription a  in
            (uu____22726, uu____22729, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____22699  in
        mk1 uu____22698
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___346_22790 = lb  in
          let uu____22791 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____22794 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___346_22790.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___346_22790.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____22791;
            FStar_Syntax_Syntax.lbeff =
              (uu___346_22790.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____22794;
            FStar_Syntax_Syntax.lbattrs =
              (uu___346_22790.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___346_22790.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____22797 =
          let uu____22798 =
            let uu____22811 =
              let uu____22818 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____22818)  in
            let uu____22827 = elim_delayed_subst_term t2  in
            (uu____22811, uu____22827)  in
          FStar_Syntax_Syntax.Tm_let uu____22798  in
        mk1 uu____22797
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____22871 =
          let uu____22872 =
            let uu____22879 = elim_delayed_subst_term tm  in
            (uu____22879, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____22872  in
        mk1 uu____22871
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____22890 =
          let uu____22891 =
            let uu____22898 = elim_delayed_subst_term t2  in
            let uu____22901 = elim_delayed_subst_meta md  in
            (uu____22898, uu____22901)  in
          FStar_Syntax_Syntax.Tm_meta uu____22891  in
        mk1 uu____22890

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___255_22910  ->
         match uu___255_22910 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____22914 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____22914
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
        let uu____22937 =
          let uu____22938 =
            let uu____22947 = elim_delayed_subst_term t  in
            (uu____22947, uopt)  in
          FStar_Syntax_Syntax.Total uu____22938  in
        mk1 uu____22937
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____22964 =
          let uu____22965 =
            let uu____22974 = elim_delayed_subst_term t  in
            (uu____22974, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____22965  in
        mk1 uu____22964
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___347_22983 = ct  in
          let uu____22984 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____22987 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____22996 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___347_22983.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___347_22983.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____22984;
            FStar_Syntax_Syntax.effect_args = uu____22987;
            FStar_Syntax_Syntax.flags = uu____22996
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___256_22999  ->
    match uu___256_22999 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____23011 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____23011
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____23044 =
          let uu____23051 = elim_delayed_subst_term t  in (m, uu____23051)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____23044
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____23063 =
          let uu____23072 = elim_delayed_subst_term t  in
          (m1, m2, uu____23072)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____23063
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____23099  ->
         match uu____23099 with
         | (t,q) ->
             let uu____23110 = elim_delayed_subst_term t  in (uu____23110, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____23130  ->
         match uu____23130 with
         | (x,q) ->
             let uu____23141 =
               let uu___348_23142 = x  in
               let uu____23143 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___348_23142.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___348_23142.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____23143
               }  in
             (uu____23141, q)) bs

let (elim_uvars_aux_tc :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.comp) FStar_Util.either
          ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
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
            | (uu____23235,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____23261,FStar_Util.Inl t) ->
                let uu____23279 =
                  let uu____23286 =
                    let uu____23287 =
                      let uu____23300 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____23300)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____23287  in
                  FStar_Syntax_Syntax.mk uu____23286  in
                uu____23279 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____23314 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____23314 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____23344 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____23407 ->
                    let uu____23408 =
                      let uu____23417 =
                        let uu____23418 = FStar_Syntax_Subst.compress t4  in
                        uu____23418.FStar_Syntax_Syntax.n  in
                      (uu____23417, tc)  in
                    (match uu____23408 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____23445) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____23486) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____23525,FStar_Util.Inl uu____23526) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____23553 -> failwith "Impossible")
                 in
              (match uu____23344 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
  
let (elim_uvars_aux_t :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.term'
                                                         FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____23678 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____23678 with
          | (univ_names1,binders1,tc) ->
              let uu____23744 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____23744)
  
let (elim_uvars_aux_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                            FStar_Pervasives_Native.tuple2
                                            Prims.list,FStar_Syntax_Syntax.comp'
                                                         FStar_Syntax_Syntax.syntax)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
          let uu____23793 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____23793 with
          | (univ_names1,binders1,tc) ->
              let uu____23859 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____23859)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____23898 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____23898 with
           | (univ_names1,binders1,typ1) ->
               let uu___349_23932 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___349_23932.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___349_23932.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___349_23932.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___349_23932.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___350_23947 = s  in
          let uu____23948 =
            let uu____23949 =
              let uu____23958 = FStar_List.map (elim_uvars env) sigs  in
              (uu____23958, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____23949  in
          {
            FStar_Syntax_Syntax.sigel = uu____23948;
            FStar_Syntax_Syntax.sigrng =
              (uu___350_23947.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___350_23947.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___350_23947.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___350_23947.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____23975 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____23975 with
           | (univ_names1,uu____23995,typ1) ->
               let uu___351_24013 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___351_24013.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___351_24013.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___351_24013.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___351_24013.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____24019 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____24019 with
           | (univ_names1,uu____24039,typ1) ->
               let uu___352_24057 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___352_24057.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___352_24057.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___352_24057.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___352_24057.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____24085 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____24085 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____24110 =
                            let uu____24111 =
                              let uu____24112 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____24112  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____24111
                             in
                          elim_delayed_subst_term uu____24110  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___353_24115 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___353_24115.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___353_24115.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___353_24115.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___353_24115.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___354_24116 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___354_24116.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___354_24116.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___354_24116.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___354_24116.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___355_24122 = s  in
          let uu____24123 =
            let uu____24124 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____24124  in
          {
            FStar_Syntax_Syntax.sigel = uu____24123;
            FStar_Syntax_Syntax.sigrng =
              (uu___355_24122.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___355_24122.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___355_24122.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___355_24122.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____24128 = elim_uvars_aux_t env us [] t  in
          (match uu____24128 with
           | (us1,uu____24148,t1) ->
               let uu___356_24166 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___356_24166.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___356_24166.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___356_24166.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___356_24166.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____24167 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____24169 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____24169 with
           | (univs1,binders,signature) ->
               let uu____24203 =
                 let uu____24208 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____24208 with
                 | (univs_opening,univs2) ->
                     let uu____24231 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____24231)
                  in
               (match uu____24203 with
                | (univs_opening,univs_closing) ->
                    let uu____24234 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____24240 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____24241 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____24240, uu____24241)  in
                    (match uu____24234 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____24265 =
                           match uu____24265 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____24283 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____24283 with
                                | (us1,t1) ->
                                    let uu____24294 =
                                      let uu____24303 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____24314 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____24303, uu____24314)  in
                                    (match uu____24294 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____24343 =
                                           let uu____24352 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____24363 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____24352, uu____24363)  in
                                         (match uu____24343 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____24393 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____24393
                                                 in
                                              let uu____24394 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____24394 with
                                               | (uu____24417,uu____24418,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____24437 =
                                                       let uu____24438 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____24438
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____24437
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____24447 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____24447 with
                           | (uu____24464,uu____24465,t1) -> t1  in
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
                             | uu____24535 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____24560 =
                               let uu____24561 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____24561.FStar_Syntax_Syntax.n  in
                             match uu____24560 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____24620 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____24651 =
                               let uu____24652 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____24652.FStar_Syntax_Syntax.n  in
                             match uu____24651 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____24673) ->
                                 let uu____24694 = destruct_action_body body
                                    in
                                 (match uu____24694 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____24739 ->
                                 let uu____24740 = destruct_action_body t  in
                                 (match uu____24740 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____24789 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____24789 with
                           | (action_univs,t) ->
                               let uu____24798 = destruct_action_typ_templ t
                                  in
                               (match uu____24798 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___357_24839 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___357_24839.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___357_24839.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___358_24841 = ed  in
                           let uu____24842 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____24843 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____24844 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____24845 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____24846 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____24847 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____24848 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____24849 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____24850 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____24851 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____24852 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____24853 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____24854 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____24855 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___358_24841.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___358_24841.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____24842;
                             FStar_Syntax_Syntax.bind_wp = uu____24843;
                             FStar_Syntax_Syntax.if_then_else = uu____24844;
                             FStar_Syntax_Syntax.ite_wp = uu____24845;
                             FStar_Syntax_Syntax.stronger = uu____24846;
                             FStar_Syntax_Syntax.close_wp = uu____24847;
                             FStar_Syntax_Syntax.assert_p = uu____24848;
                             FStar_Syntax_Syntax.assume_p = uu____24849;
                             FStar_Syntax_Syntax.null_wp = uu____24850;
                             FStar_Syntax_Syntax.trivial = uu____24851;
                             FStar_Syntax_Syntax.repr = uu____24852;
                             FStar_Syntax_Syntax.return_repr = uu____24853;
                             FStar_Syntax_Syntax.bind_repr = uu____24854;
                             FStar_Syntax_Syntax.actions = uu____24855;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___358_24841.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___359_24858 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___359_24858.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___359_24858.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___359_24858.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___359_24858.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___257_24879 =
            match uu___257_24879 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____24910 = elim_uvars_aux_t env us [] t  in
                (match uu____24910 with
                 | (us1,uu____24938,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___360_24965 = sub_eff  in
            let uu____24966 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____24969 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___360_24965.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___360_24965.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____24966;
              FStar_Syntax_Syntax.lift = uu____24969
            }  in
          let uu___361_24972 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___361_24972.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___361_24972.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___361_24972.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___361_24972.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____24982 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____24982 with
           | (univ_names1,binders1,comp1) ->
               let uu___362_25016 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___362_25016.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___362_25016.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___362_25016.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___362_25016.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____25019 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____25020 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      normalize
        [FStar_TypeChecker_Env.EraseUniverses;
        FStar_TypeChecker_Env.AllowUnboundUniverses] env t
  