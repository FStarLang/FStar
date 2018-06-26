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
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___249_5790  ->
    match uu___249_5790 with
    | (App
        (uu____5793,{
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reify );
                      FStar_Syntax_Syntax.pos = uu____5794;
                      FStar_Syntax_Syntax.vars = uu____5795;_},uu____5796,uu____5797))::uu____5798
        -> true
    | uu____5803 -> false
  
let firstn :
  'Auu____5812 .
    Prims.int ->
      'Auu____5812 Prims.list ->
        ('Auu____5812 Prims.list,'Auu____5812 Prims.list)
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
          (uu____5854,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____5855;
                        FStar_Syntax_Syntax.vars = uu____5856;_},uu____5857,uu____5858))::uu____5859
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____5864 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____5887) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____5897) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____5916  ->
                  match uu____5916 with
                  | (a,uu____5924) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____5930 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____5953 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____5954 -> false
    | FStar_Syntax_Syntax.Tm_type uu____5967 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____5968 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____5969 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____5970 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____5971 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____5972 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____5979 -> false
    | FStar_Syntax_Syntax.Tm_let uu____5986 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____5999 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____6016 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____6029 -> true
    | FStar_Syntax_Syntax.Tm_match uu____6036 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____6098  ->
                   match uu____6098 with
                   | (a,uu____6106) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____6113) ->
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
                     (fun uu____6235  ->
                        match uu____6235 with
                        | (a,uu____6243) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____6248,uu____6249,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____6255,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____6261 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____6268 -> false
            | FStar_Syntax_Syntax.Meta_named uu____6269 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____6275 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____6281 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_fully  -> true | uu____6287 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_reify  -> true | uu____6293 -> false
  
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
            let uu____6322 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
            match uu____6322 with
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
              (fun uu____6450  ->
                 fun uu____6451  ->
                   match (uu____6450, uu____6451) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____6511 =
            match uu____6511 with
            | (x,y,z) ->
                let uu____6521 = FStar_Util.string_of_bool x  in
                let uu____6522 = FStar_Util.string_of_bool y  in
                let uu____6523 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____6521 uu____6522
                  uu____6523
             in
          let res =
            match (qninfo,
                    ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only),
                    ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully),
                    ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr))
            with
            | uu____6569 when FStar_TypeChecker_Env.qninfo_is_action qninfo
                ->
                let b = should_reify1 cfg  in
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____6615  ->
                      let uu____6616 = FStar_Syntax_Print.fv_to_string fv  in
                      let uu____6617 = FStar_Util.string_of_bool b  in
                      FStar_Util.print2
                        "should_unfold: For DM4F action %s, should_reify = %s\n"
                        uu____6616 uu____6617);
                 if b then reif else no)
            | uu____6625 when
                let uu____6666 = FStar_TypeChecker_Cfg.find_prim_step cfg fv
                   in
                FStar_Option.isSome uu____6666 ->
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____6671  ->
                      FStar_Util.print_string
                        "should_unfold: primitive step, no\n");
                 no)
            | (FStar_Pervasives_Native.Some
               (FStar_Util.Inr
                ({
                   FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                     ((is_rec,uu____6673),uu____6674);
                   FStar_Syntax_Syntax.sigrng = uu____6675;
                   FStar_Syntax_Syntax.sigquals = qs;
                   FStar_Syntax_Syntax.sigmeta = uu____6677;
                   FStar_Syntax_Syntax.sigattrs = uu____6678;_},uu____6679),uu____6680),uu____6681,uu____6682,uu____6683)
                when
                FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect qs ->
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____6788  ->
                      FStar_Util.print_string
                        "should_unfold: masked effect, no\n");
                 no)
            | (uu____6789,uu____6790,uu____6791,uu____6792) when
                (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                  &&
                  (FStar_Util.for_some
                     (FStar_Syntax_Util.attr_eq
                        FStar_Syntax_Util.tac_opaque_attr) attrs)
                ->
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____6859  ->
                      FStar_Util.print_string
                        "should_unfold: masked effect, no\n");
                 no)
            | (FStar_Pervasives_Native.Some
               (FStar_Util.Inr
                ({
                   FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                     ((is_rec,uu____6861),uu____6862);
                   FStar_Syntax_Syntax.sigrng = uu____6863;
                   FStar_Syntax_Syntax.sigquals = qs;
                   FStar_Syntax_Syntax.sigmeta = uu____6865;
                   FStar_Syntax_Syntax.sigattrs = uu____6866;_},uu____6867),uu____6868),uu____6869,uu____6870,uu____6871)
                when
                is_rec &&
                  (Prims.op_Negation
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                ->
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____6976  ->
                      FStar_Util.print_string
                        "should_unfold: recursive function without zeta, no\n");
                 no)
            | (uu____6977,FStar_Pervasives_Native.Some
               uu____6978,uu____6979,uu____6980) ->
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7048  ->
                      let uu____7049 = FStar_Syntax_Print.fv_to_string fv  in
                      FStar_Util.print1
                        "should_unfold: Reached a %s with selective unfolding\n"
                        uu____7049);
                 (let uu____7050 =
                    let uu____7059 =
                      match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                      with
                      | FStar_Pervasives_Native.None  -> no
                      | FStar_Pervasives_Native.Some lids ->
                          let uu____7079 =
                            FStar_Util.for_some
                              (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                             in
                          FStar_All.pipe_left yesno uu____7079
                       in
                    let uu____7086 =
                      let uu____7095 =
                        match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                        with
                        | FStar_Pervasives_Native.None  -> no
                        | FStar_Pervasives_Native.Some ats ->
                            let uu____7115 =
                              FStar_Util.for_some
                                (fun at  ->
                                   FStar_Util.for_some
                                     (FStar_Syntax_Util.attr_eq at) ats)
                                attrs
                               in
                            FStar_All.pipe_left yesno uu____7115
                         in
                      let uu____7124 =
                        let uu____7133 =
                          match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                          with
                          | FStar_Pervasives_Native.None  -> no
                          | FStar_Pervasives_Native.Some lids ->
                              let uu____7153 =
                                FStar_Util.for_some
                                  (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                 in
                              FStar_All.pipe_left fullyno uu____7153
                           in
                        [uu____7133]  in
                      uu____7095 :: uu____7124  in
                    uu____7059 :: uu____7086  in
                  comb_or uu____7050))
            | (uu____7184,uu____7185,FStar_Pervasives_Native.Some
               uu____7186,uu____7187) ->
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7255  ->
                      let uu____7256 = FStar_Syntax_Print.fv_to_string fv  in
                      FStar_Util.print1
                        "should_unfold: Reached a %s with selective unfolding\n"
                        uu____7256);
                 (let uu____7257 =
                    let uu____7266 =
                      match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                      with
                      | FStar_Pervasives_Native.None  -> no
                      | FStar_Pervasives_Native.Some lids ->
                          let uu____7286 =
                            FStar_Util.for_some
                              (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                             in
                          FStar_All.pipe_left yesno uu____7286
                       in
                    let uu____7293 =
                      let uu____7302 =
                        match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                        with
                        | FStar_Pervasives_Native.None  -> no
                        | FStar_Pervasives_Native.Some ats ->
                            let uu____7322 =
                              FStar_Util.for_some
                                (fun at  ->
                                   FStar_Util.for_some
                                     (FStar_Syntax_Util.attr_eq at) ats)
                                attrs
                               in
                            FStar_All.pipe_left yesno uu____7322
                         in
                      let uu____7331 =
                        let uu____7340 =
                          match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                          with
                          | FStar_Pervasives_Native.None  -> no
                          | FStar_Pervasives_Native.Some lids ->
                              let uu____7360 =
                                FStar_Util.for_some
                                  (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                 in
                              FStar_All.pipe_left fullyno uu____7360
                           in
                        [uu____7340]  in
                      uu____7302 :: uu____7331  in
                    uu____7266 :: uu____7293  in
                  comb_or uu____7257))
            | (uu____7391,uu____7392,uu____7393,FStar_Pervasives_Native.Some
               uu____7394) ->
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7462  ->
                      let uu____7463 = FStar_Syntax_Print.fv_to_string fv  in
                      FStar_Util.print1
                        "should_unfold: Reached a %s with selective unfolding\n"
                        uu____7463);
                 (let uu____7464 =
                    let uu____7473 =
                      match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                      with
                      | FStar_Pervasives_Native.None  -> no
                      | FStar_Pervasives_Native.Some lids ->
                          let uu____7493 =
                            FStar_Util.for_some
                              (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                             in
                          FStar_All.pipe_left yesno uu____7493
                       in
                    let uu____7500 =
                      let uu____7509 =
                        match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                        with
                        | FStar_Pervasives_Native.None  -> no
                        | FStar_Pervasives_Native.Some ats ->
                            let uu____7529 =
                              FStar_Util.for_some
                                (fun at  ->
                                   FStar_Util.for_some
                                     (FStar_Syntax_Util.attr_eq at) ats)
                                attrs
                               in
                            FStar_All.pipe_left yesno uu____7529
                         in
                      let uu____7538 =
                        let uu____7547 =
                          match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                          with
                          | FStar_Pervasives_Native.None  -> no
                          | FStar_Pervasives_Native.Some lids ->
                              let uu____7567 =
                                FStar_Util.for_some
                                  (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                 in
                              FStar_All.pipe_left fullyno uu____7567
                           in
                        [uu____7547]  in
                      uu____7509 :: uu____7538  in
                    uu____7473 :: uu____7500  in
                  comb_or uu____7464))
            | uu____7598 ->
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7644  ->
                      let uu____7645 = FStar_Syntax_Print.fv_to_string fv  in
                      let uu____7646 =
                        FStar_Syntax_Print.delta_depth_to_string
                          fv.FStar_Syntax_Syntax.fv_delta
                         in
                      let uu____7647 =
                        FStar_Common.string_of_list
                          FStar_TypeChecker_Env.string_of_delta_level
                          cfg.FStar_TypeChecker_Cfg.delta_level
                         in
                      FStar_Util.print3
                        "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                        uu____7645 uu____7646 uu____7647);
                 (let uu____7648 =
                    FStar_All.pipe_right
                      cfg.FStar_TypeChecker_Cfg.delta_level
                      (FStar_Util.for_some
                         (fun uu___250_7652  ->
                            match uu___250_7652 with
                            | FStar_TypeChecker_Env.UnfoldTacDelta  -> false
                            | FStar_TypeChecker_Env.NoDelta  -> false
                            | FStar_TypeChecker_Env.InliningDelta  -> true
                            | FStar_TypeChecker_Env.Eager_unfolding_only  ->
                                true
                            | FStar_TypeChecker_Env.Unfold l ->
                                FStar_TypeChecker_Common.delta_depth_greater_than
                                  fv.FStar_Syntax_Syntax.fv_delta l))
                     in
                  FStar_All.pipe_left yesno uu____7648))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____7665  ->
               let uu____7666 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____7667 =
                 let uu____7668 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____7668  in
               let uu____7669 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____7666 uu____7667 uu____7669);
          (match res with
           | (false ,uu____7670,uu____7671) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____7672 ->
               let uu____7679 =
                 let uu____7680 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____7680
                  in
               FStar_All.pipe_left failwith uu____7679)
  
let decide_unfolding :
  'Auu____7697 'Auu____7698 .
    FStar_TypeChecker_Cfg.cfg ->
      'Auu____7697 ->
        stack_elt Prims.list ->
          'Auu____7698 ->
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
                    let uu___283_7767 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___284_7770 = cfg.FStar_TypeChecker_Cfg.steps
                            in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___284_7770.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___284_7770.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___284_7770.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___284_7770.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___284_7770.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___284_7770.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___284_7770.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___284_7770.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___284_7770.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___284_7770.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___284_7770.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___284_7770.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___284_7770.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___284_7770.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___284_7770.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___284_7770.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___284_7770.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___284_7770.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___284_7770.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___284_7770.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___284_7770.FStar_TypeChecker_Cfg.nbe_step)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___283_7767.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___283_7767.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___283_7767.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___283_7767.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___283_7767.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___283_7767.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___283_7767.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___283_7767.FStar_TypeChecker_Cfg.reifying)
                    }  in
                  let stack' = (Cfg cfg) :: stack  in
                  FStar_Pervasives_Native.Some (cfg', stack')
              | Should_unfold_reify  ->
                  let uu____7788 =
                    let uu____7795 = FStar_List.tl stack  in
                    (cfg, uu____7795)  in
                  FStar_Pervasives_Native.Some uu____7788
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____8097 ->
                   let uu____8120 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____8120
               | uu____8121 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____8129  ->
               let uu____8130 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____8131 = FStar_Syntax_Print.term_to_string t1  in
               let uu____8132 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____8139 =
                 let uu____8140 =
                   let uu____8143 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____8143
                    in
                 stack_to_string uu____8140  in
               FStar_Util.print4
                 ">>> %s\nNorm %s with with %s env elements top of the stack %s \n"
                 uu____8130 uu____8131 uu____8132 uu____8139);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8169  ->
                     let uu____8170 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8170);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____8171 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8175  ->
                     let uu____8176 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8176);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____8177 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8181  ->
                     let uu____8182 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8182);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____8183 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8187  ->
                     let uu____8188 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8188);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8189;
                 FStar_Syntax_Syntax.fv_delta =
                   FStar_Syntax_Syntax.Delta_constant_at_level _0_17;
                 FStar_Syntax_Syntax.fv_qual = uu____8190;_}
               when _0_17 = (Prims.parse_int "0") ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8196  ->
                     let uu____8197 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8197);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8198;
                 FStar_Syntax_Syntax.fv_delta = uu____8199;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8203  ->
                     let uu____8204 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8204);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____8205;
                 FStar_Syntax_Syntax.fv_delta = uu____8206;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____8207);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____8217  ->
                     let uu____8218 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____8218);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let qninfo =
                 let uu____8221 = FStar_Syntax_Syntax.lid_of_fv fv  in
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv uu____8221
                  in
               let uu____8222 =
                 decide_unfolding cfg env stack t1.FStar_Syntax_Syntax.pos fv
                   qninfo
                  in
               (match uu____8222 with
                | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                    do_unfold_fv cfg1 env stack1 t1 qninfo fv
                | FStar_Pervasives_Native.None  -> rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_quoted uu____8249 ->
               let uu____8256 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____8256
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               ((Prims.op_Negation
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
                  && (is_norm_request hd1 args))
                 &&
                 (let uu____8286 =
                    FStar_Ident.lid_equals
                      (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
                      FStar_Parser_Const.prims_lid
                     in
                  Prims.op_Negation uu____8286)
               ->
               (FStar_TypeChecker_Cfg.log_nbe cfg
                  (fun uu____8290  ->
                     let uu____8291 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "Reached norm_request for %s\n"
                       uu____8291);
                (let cfg' =
                   let uu___285_8293 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___286_8296 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___286_8296.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___286_8296.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___286_8296.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___286_8296.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___286_8296.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___286_8296.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___286_8296.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___286_8296.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___286_8296.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___286_8296.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___286_8296.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___286_8296.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___286_8296.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___286_8296.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___286_8296.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___286_8296.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___286_8296.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___286_8296.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___286_8296.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___286_8296.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___286_8296.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___286_8296.FStar_TypeChecker_Cfg.nbe_step)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___285_8293.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___285_8293.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___285_8293.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___285_8293.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___285_8293.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___285_8293.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____8301 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____8301 with
                 | FStar_Pervasives_Native.None  ->
                     let stack1 =
                       FStar_All.pipe_right stack
                         (FStar_List.fold_right
                            (fun uu____8330  ->
                               fun stack1  ->
                                 match uu____8330 with
                                 | (a,aq) ->
                                     let uu____8342 =
                                       let uu____8343 =
                                         let uu____8350 =
                                           let uu____8351 =
                                             let uu____8382 =
                                               FStar_Util.mk_ref
                                                 FStar_Pervasives_Native.None
                                                in
                                             (env, a, uu____8382, false)  in
                                           Clos uu____8351  in
                                         (uu____8350, aq,
                                           (t1.FStar_Syntax_Syntax.pos))
                                          in
                                       Arg uu____8343  in
                                     uu____8342 :: stack1) args)
                        in
                     (FStar_TypeChecker_Cfg.log cfg
                        (fun uu____8470  ->
                           let uu____8471 =
                             FStar_All.pipe_left FStar_Util.string_of_int
                               (FStar_List.length args)
                              in
                           FStar_Util.print1 "\tPushed %s arguments\n"
                             uu____8471);
                      norm cfg env stack1 hd1)
                 | FStar_Pervasives_Native.Some (s,tm) when is_nbe_request s
                     ->
                     let delta_level =
                       let uu____8493 =
                         FStar_All.pipe_right s
                           (FStar_Util.for_some
                              (fun uu___251_8498  ->
                                 match uu___251_8498 with
                                 | FStar_TypeChecker_Env.UnfoldUntil
                                     uu____8499 -> true
                                 | FStar_TypeChecker_Env.UnfoldOnly
                                     uu____8500 -> true
                                 | FStar_TypeChecker_Env.UnfoldFully
                                     uu____8503 -> true
                                 | uu____8506 -> false))
                          in
                       if uu____8493
                       then
                         [FStar_TypeChecker_Env.Unfold
                            FStar_Syntax_Syntax.delta_constant]
                       else [FStar_TypeChecker_Env.NoDelta]  in
                     let tm' = closure_as_term cfg env tm  in
                     (FStar_TypeChecker_Cfg.log_nbe cfg
                        (fun uu____8514  ->
                           let uu____8515 =
                             FStar_Syntax_Print.term_to_string tm'  in
                           FStar_Util.print1 "Invoking NBE with  %s\n"
                             uu____8515);
                      (let tm_norm =
                         let uu____8517 =
                           let uu____8532 = FStar_TypeChecker_Cfg.cfg_env cfg
                              in
                           uu____8532.FStar_TypeChecker_Env.nbe  in
                         uu____8517 s cfg.FStar_TypeChecker_Cfg.tcenv tm'  in
                       FStar_TypeChecker_Cfg.log_nbe cfg
                         (fun uu____8536  ->
                            let uu____8537 =
                              FStar_Syntax_Print.term_to_string tm_norm  in
                            FStar_Util.print1 "Result of NBE is  %s\n"
                              uu____8537);
                       norm cfg env stack tm_norm))
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     let delta_level =
                       let uu____8553 =
                         FStar_All.pipe_right s
                           (FStar_Util.for_some
                              (fun uu___252_8558  ->
                                 match uu___252_8558 with
                                 | FStar_TypeChecker_Env.UnfoldUntil
                                     uu____8559 -> true
                                 | FStar_TypeChecker_Env.UnfoldOnly
                                     uu____8560 -> true
                                 | FStar_TypeChecker_Env.UnfoldFully
                                     uu____8563 -> true
                                 | uu____8566 -> false))
                          in
                       if uu____8553
                       then
                         [FStar_TypeChecker_Env.Unfold
                            FStar_Syntax_Syntax.delta_constant]
                       else [FStar_TypeChecker_Env.NoDelta]  in
                     let cfg'1 =
                       let uu___287_8571 = cfg  in
                       let uu____8572 =
                         let uu___288_8573 =
                           FStar_TypeChecker_Cfg.to_fsteps s  in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___288_8573.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___288_8573.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___288_8573.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___288_8573.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___288_8573.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___288_8573.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___288_8573.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                           FStar_TypeChecker_Cfg.unfold_until =
                             (uu___288_8573.FStar_TypeChecker_Cfg.unfold_until);
                           FStar_TypeChecker_Cfg.unfold_only =
                             (uu___288_8573.FStar_TypeChecker_Cfg.unfold_only);
                           FStar_TypeChecker_Cfg.unfold_fully =
                             (uu___288_8573.FStar_TypeChecker_Cfg.unfold_fully);
                           FStar_TypeChecker_Cfg.unfold_attr =
                             (uu___288_8573.FStar_TypeChecker_Cfg.unfold_attr);
                           FStar_TypeChecker_Cfg.unfold_tac =
                             (uu___288_8573.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___288_8573.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___288_8573.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___288_8573.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___288_8573.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___288_8573.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___288_8573.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___288_8573.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___288_8573.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___288_8573.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___288_8573.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request = true;
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___288_8573.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___288_8573.FStar_TypeChecker_Cfg.nbe_step)
                         }  in
                       {
                         FStar_TypeChecker_Cfg.steps = uu____8572;
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___287_8571.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___287_8571.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level = delta_level;
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___287_8571.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___287_8571.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___287_8571.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                         FStar_TypeChecker_Cfg.reifying =
                           (uu___287_8571.FStar_TypeChecker_Cfg.reifying)
                       }  in
                     let stack' =
                       let tail1 = (Cfg cfg) :: stack  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         let uu____8578 =
                           let uu____8579 =
                             let uu____8584 = FStar_Util.now ()  in
                             (t1, uu____8584)  in
                           Debug uu____8579  in
                         uu____8578 :: tail1
                       else tail1  in
                     norm cfg'1 env stack' tm))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____8588 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____8588
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____8597 =
                      let uu____8604 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____8604, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____8597  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____8613 = lookup_bvar env x  in
               (match uu____8613 with
                | Univ uu____8614 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                    then
                      let uu____8663 = FStar_ST.op_Bang r  in
                      (match uu____8663 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____8785  ->
                                 let uu____8786 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____8787 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____8786
                                   uu____8787);
                            (let uu____8788 = maybe_weakly_reduced t'  in
                             if uu____8788
                             then
                               match stack with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____8789 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____8860)::uu____8861 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____8871,uu____8872))::stack_rest ->
                    (match c with
                     | Univ uu____8876 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____8885 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____8906  ->
                                    let uu____8907 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____8907);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____8935  ->
                                    let uu____8936 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____8936);
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
                       (fun uu____9002  ->
                          let uu____9003 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____9003);
                     norm cfg env stack1 t1)
                | (Match uu____9004)::uu____9005 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 =
                        if
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___289_9019 =
                               cfg.FStar_TypeChecker_Cfg.steps  in
                             {
                               FStar_TypeChecker_Cfg.beta =
                                 (uu___289_9019.FStar_TypeChecker_Cfg.beta);
                               FStar_TypeChecker_Cfg.iota = false;
                               FStar_TypeChecker_Cfg.zeta = false;
                               FStar_TypeChecker_Cfg.weak = false;
                               FStar_TypeChecker_Cfg.hnf =
                                 (uu___289_9019.FStar_TypeChecker_Cfg.hnf);
                               FStar_TypeChecker_Cfg.primops = false;
                               FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                 = true;
                               FStar_TypeChecker_Cfg.unfold_until =
                                 (uu___289_9019.FStar_TypeChecker_Cfg.unfold_until);
                               FStar_TypeChecker_Cfg.unfold_only =
                                 (uu___289_9019.FStar_TypeChecker_Cfg.unfold_only);
                               FStar_TypeChecker_Cfg.unfold_fully =
                                 (uu___289_9019.FStar_TypeChecker_Cfg.unfold_fully);
                               FStar_TypeChecker_Cfg.unfold_attr =
                                 (uu___289_9019.FStar_TypeChecker_Cfg.unfold_attr);
                               FStar_TypeChecker_Cfg.unfold_tac =
                                 (uu___289_9019.FStar_TypeChecker_Cfg.unfold_tac);
                               FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                 = false;
                               FStar_TypeChecker_Cfg.simplify = false;
                               FStar_TypeChecker_Cfg.erase_universes =
                                 (uu___289_9019.FStar_TypeChecker_Cfg.erase_universes);
                               FStar_TypeChecker_Cfg.allow_unbound_universes
                                 =
                                 (uu___289_9019.FStar_TypeChecker_Cfg.allow_unbound_universes);
                               FStar_TypeChecker_Cfg.reify_ = false;
                               FStar_TypeChecker_Cfg.compress_uvars =
                                 (uu___289_9019.FStar_TypeChecker_Cfg.compress_uvars);
                               FStar_TypeChecker_Cfg.no_full_norm = true;
                               FStar_TypeChecker_Cfg.check_no_uvars =
                                 (uu___289_9019.FStar_TypeChecker_Cfg.check_no_uvars);
                               FStar_TypeChecker_Cfg.unmeta = false;
                               FStar_TypeChecker_Cfg.unascribe = false;
                               FStar_TypeChecker_Cfg.in_full_norm_request =
                                 (uu___289_9019.FStar_TypeChecker_Cfg.in_full_norm_request);
                               FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                 =
                                 (uu___289_9019.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                               FStar_TypeChecker_Cfg.nbe_step =
                                 (uu___289_9019.FStar_TypeChecker_Cfg.nbe_step)
                             }  in
                           let cfg' =
                             let uu___290_9021 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps = steps';
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___290_9021.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___290_9021.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 [FStar_TypeChecker_Env.NoDelta];
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___290_9021.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong =
                                 (uu___290_9021.FStar_TypeChecker_Cfg.strong);
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___290_9021.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___290_9021.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___290_9021.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____9023 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9023 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9055  -> dummy :: env1) env)
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
                                          let uu____9096 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9096)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___291_9103 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___291_9103.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___291_9103.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9104 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9110  ->
                                 let uu____9111 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9111);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___292_9120 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___292_9120.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___292_9120.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___292_9120.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___292_9120.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___292_9120.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___292_9120.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___292_9120.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___292_9120.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____9123)::uu____9124 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 =
                        if
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___289_9134 =
                               cfg.FStar_TypeChecker_Cfg.steps  in
                             {
                               FStar_TypeChecker_Cfg.beta =
                                 (uu___289_9134.FStar_TypeChecker_Cfg.beta);
                               FStar_TypeChecker_Cfg.iota = false;
                               FStar_TypeChecker_Cfg.zeta = false;
                               FStar_TypeChecker_Cfg.weak = false;
                               FStar_TypeChecker_Cfg.hnf =
                                 (uu___289_9134.FStar_TypeChecker_Cfg.hnf);
                               FStar_TypeChecker_Cfg.primops = false;
                               FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                 = true;
                               FStar_TypeChecker_Cfg.unfold_until =
                                 (uu___289_9134.FStar_TypeChecker_Cfg.unfold_until);
                               FStar_TypeChecker_Cfg.unfold_only =
                                 (uu___289_9134.FStar_TypeChecker_Cfg.unfold_only);
                               FStar_TypeChecker_Cfg.unfold_fully =
                                 (uu___289_9134.FStar_TypeChecker_Cfg.unfold_fully);
                               FStar_TypeChecker_Cfg.unfold_attr =
                                 (uu___289_9134.FStar_TypeChecker_Cfg.unfold_attr);
                               FStar_TypeChecker_Cfg.unfold_tac =
                                 (uu___289_9134.FStar_TypeChecker_Cfg.unfold_tac);
                               FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                 = false;
                               FStar_TypeChecker_Cfg.simplify = false;
                               FStar_TypeChecker_Cfg.erase_universes =
                                 (uu___289_9134.FStar_TypeChecker_Cfg.erase_universes);
                               FStar_TypeChecker_Cfg.allow_unbound_universes
                                 =
                                 (uu___289_9134.FStar_TypeChecker_Cfg.allow_unbound_universes);
                               FStar_TypeChecker_Cfg.reify_ = false;
                               FStar_TypeChecker_Cfg.compress_uvars =
                                 (uu___289_9134.FStar_TypeChecker_Cfg.compress_uvars);
                               FStar_TypeChecker_Cfg.no_full_norm = true;
                               FStar_TypeChecker_Cfg.check_no_uvars =
                                 (uu___289_9134.FStar_TypeChecker_Cfg.check_no_uvars);
                               FStar_TypeChecker_Cfg.unmeta = false;
                               FStar_TypeChecker_Cfg.unascribe = false;
                               FStar_TypeChecker_Cfg.in_full_norm_request =
                                 (uu___289_9134.FStar_TypeChecker_Cfg.in_full_norm_request);
                               FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                 =
                                 (uu___289_9134.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                               FStar_TypeChecker_Cfg.nbe_step =
                                 (uu___289_9134.FStar_TypeChecker_Cfg.nbe_step)
                             }  in
                           let cfg' =
                             let uu___290_9136 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps = steps';
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___290_9136.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___290_9136.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 [FStar_TypeChecker_Env.NoDelta];
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___290_9136.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong =
                                 (uu___290_9136.FStar_TypeChecker_Cfg.strong);
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___290_9136.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___290_9136.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___290_9136.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____9138 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9138 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9170  -> dummy :: env1) env)
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
                                          let uu____9211 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9211)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___291_9218 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___291_9218.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___291_9218.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9219 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9225  ->
                                 let uu____9226 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9226);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___292_9235 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___292_9235.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___292_9235.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___292_9235.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___292_9235.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___292_9235.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___292_9235.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___292_9235.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___292_9235.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____9238)::uu____9239 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 =
                        if
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___289_9251 =
                               cfg.FStar_TypeChecker_Cfg.steps  in
                             {
                               FStar_TypeChecker_Cfg.beta =
                                 (uu___289_9251.FStar_TypeChecker_Cfg.beta);
                               FStar_TypeChecker_Cfg.iota = false;
                               FStar_TypeChecker_Cfg.zeta = false;
                               FStar_TypeChecker_Cfg.weak = false;
                               FStar_TypeChecker_Cfg.hnf =
                                 (uu___289_9251.FStar_TypeChecker_Cfg.hnf);
                               FStar_TypeChecker_Cfg.primops = false;
                               FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                 = true;
                               FStar_TypeChecker_Cfg.unfold_until =
                                 (uu___289_9251.FStar_TypeChecker_Cfg.unfold_until);
                               FStar_TypeChecker_Cfg.unfold_only =
                                 (uu___289_9251.FStar_TypeChecker_Cfg.unfold_only);
                               FStar_TypeChecker_Cfg.unfold_fully =
                                 (uu___289_9251.FStar_TypeChecker_Cfg.unfold_fully);
                               FStar_TypeChecker_Cfg.unfold_attr =
                                 (uu___289_9251.FStar_TypeChecker_Cfg.unfold_attr);
                               FStar_TypeChecker_Cfg.unfold_tac =
                                 (uu___289_9251.FStar_TypeChecker_Cfg.unfold_tac);
                               FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                 = false;
                               FStar_TypeChecker_Cfg.simplify = false;
                               FStar_TypeChecker_Cfg.erase_universes =
                                 (uu___289_9251.FStar_TypeChecker_Cfg.erase_universes);
                               FStar_TypeChecker_Cfg.allow_unbound_universes
                                 =
                                 (uu___289_9251.FStar_TypeChecker_Cfg.allow_unbound_universes);
                               FStar_TypeChecker_Cfg.reify_ = false;
                               FStar_TypeChecker_Cfg.compress_uvars =
                                 (uu___289_9251.FStar_TypeChecker_Cfg.compress_uvars);
                               FStar_TypeChecker_Cfg.no_full_norm = true;
                               FStar_TypeChecker_Cfg.check_no_uvars =
                                 (uu___289_9251.FStar_TypeChecker_Cfg.check_no_uvars);
                               FStar_TypeChecker_Cfg.unmeta = false;
                               FStar_TypeChecker_Cfg.unascribe = false;
                               FStar_TypeChecker_Cfg.in_full_norm_request =
                                 (uu___289_9251.FStar_TypeChecker_Cfg.in_full_norm_request);
                               FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                 =
                                 (uu___289_9251.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                               FStar_TypeChecker_Cfg.nbe_step =
                                 (uu___289_9251.FStar_TypeChecker_Cfg.nbe_step)
                             }  in
                           let cfg' =
                             let uu___290_9253 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps = steps';
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___290_9253.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___290_9253.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 [FStar_TypeChecker_Env.NoDelta];
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___290_9253.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong =
                                 (uu___290_9253.FStar_TypeChecker_Cfg.strong);
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___290_9253.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___290_9253.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___290_9253.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____9255 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9255 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9287  -> dummy :: env1) env)
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
                                          let uu____9328 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9328)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___291_9335 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___291_9335.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___291_9335.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9336 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9342  ->
                                 let uu____9343 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9343);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___292_9352 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___292_9352.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___292_9352.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___292_9352.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___292_9352.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___292_9352.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___292_9352.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___292_9352.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___292_9352.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____9355)::uu____9356 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 =
                        if
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___289_9370 =
                               cfg.FStar_TypeChecker_Cfg.steps  in
                             {
                               FStar_TypeChecker_Cfg.beta =
                                 (uu___289_9370.FStar_TypeChecker_Cfg.beta);
                               FStar_TypeChecker_Cfg.iota = false;
                               FStar_TypeChecker_Cfg.zeta = false;
                               FStar_TypeChecker_Cfg.weak = false;
                               FStar_TypeChecker_Cfg.hnf =
                                 (uu___289_9370.FStar_TypeChecker_Cfg.hnf);
                               FStar_TypeChecker_Cfg.primops = false;
                               FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                 = true;
                               FStar_TypeChecker_Cfg.unfold_until =
                                 (uu___289_9370.FStar_TypeChecker_Cfg.unfold_until);
                               FStar_TypeChecker_Cfg.unfold_only =
                                 (uu___289_9370.FStar_TypeChecker_Cfg.unfold_only);
                               FStar_TypeChecker_Cfg.unfold_fully =
                                 (uu___289_9370.FStar_TypeChecker_Cfg.unfold_fully);
                               FStar_TypeChecker_Cfg.unfold_attr =
                                 (uu___289_9370.FStar_TypeChecker_Cfg.unfold_attr);
                               FStar_TypeChecker_Cfg.unfold_tac =
                                 (uu___289_9370.FStar_TypeChecker_Cfg.unfold_tac);
                               FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                 = false;
                               FStar_TypeChecker_Cfg.simplify = false;
                               FStar_TypeChecker_Cfg.erase_universes =
                                 (uu___289_9370.FStar_TypeChecker_Cfg.erase_universes);
                               FStar_TypeChecker_Cfg.allow_unbound_universes
                                 =
                                 (uu___289_9370.FStar_TypeChecker_Cfg.allow_unbound_universes);
                               FStar_TypeChecker_Cfg.reify_ = false;
                               FStar_TypeChecker_Cfg.compress_uvars =
                                 (uu___289_9370.FStar_TypeChecker_Cfg.compress_uvars);
                               FStar_TypeChecker_Cfg.no_full_norm = true;
                               FStar_TypeChecker_Cfg.check_no_uvars =
                                 (uu___289_9370.FStar_TypeChecker_Cfg.check_no_uvars);
                               FStar_TypeChecker_Cfg.unmeta = false;
                               FStar_TypeChecker_Cfg.unascribe = false;
                               FStar_TypeChecker_Cfg.in_full_norm_request =
                                 (uu___289_9370.FStar_TypeChecker_Cfg.in_full_norm_request);
                               FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                 =
                                 (uu___289_9370.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                               FStar_TypeChecker_Cfg.nbe_step =
                                 (uu___289_9370.FStar_TypeChecker_Cfg.nbe_step)
                             }  in
                           let cfg' =
                             let uu___290_9372 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps = steps';
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___290_9372.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___290_9372.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 [FStar_TypeChecker_Env.NoDelta];
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___290_9372.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong =
                                 (uu___290_9372.FStar_TypeChecker_Cfg.strong);
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___290_9372.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___290_9372.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___290_9372.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           norm cfg' env [] t1)
                         in
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
                                     fun uu____9406  -> dummy :: env1) env)
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
                                          let uu____9447 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9447)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___291_9454 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___291_9454.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___291_9454.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9455 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9461  ->
                                 let uu____9462 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9462);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___292_9471 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___292_9471.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___292_9471.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___292_9471.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___292_9471.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___292_9471.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___292_9471.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___292_9471.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___292_9471.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____9474)::uu____9475 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 =
                        if
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___289_9489 =
                               cfg.FStar_TypeChecker_Cfg.steps  in
                             {
                               FStar_TypeChecker_Cfg.beta =
                                 (uu___289_9489.FStar_TypeChecker_Cfg.beta);
                               FStar_TypeChecker_Cfg.iota = false;
                               FStar_TypeChecker_Cfg.zeta = false;
                               FStar_TypeChecker_Cfg.weak = false;
                               FStar_TypeChecker_Cfg.hnf =
                                 (uu___289_9489.FStar_TypeChecker_Cfg.hnf);
                               FStar_TypeChecker_Cfg.primops = false;
                               FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                 = true;
                               FStar_TypeChecker_Cfg.unfold_until =
                                 (uu___289_9489.FStar_TypeChecker_Cfg.unfold_until);
                               FStar_TypeChecker_Cfg.unfold_only =
                                 (uu___289_9489.FStar_TypeChecker_Cfg.unfold_only);
                               FStar_TypeChecker_Cfg.unfold_fully =
                                 (uu___289_9489.FStar_TypeChecker_Cfg.unfold_fully);
                               FStar_TypeChecker_Cfg.unfold_attr =
                                 (uu___289_9489.FStar_TypeChecker_Cfg.unfold_attr);
                               FStar_TypeChecker_Cfg.unfold_tac =
                                 (uu___289_9489.FStar_TypeChecker_Cfg.unfold_tac);
                               FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                 = false;
                               FStar_TypeChecker_Cfg.simplify = false;
                               FStar_TypeChecker_Cfg.erase_universes =
                                 (uu___289_9489.FStar_TypeChecker_Cfg.erase_universes);
                               FStar_TypeChecker_Cfg.allow_unbound_universes
                                 =
                                 (uu___289_9489.FStar_TypeChecker_Cfg.allow_unbound_universes);
                               FStar_TypeChecker_Cfg.reify_ = false;
                               FStar_TypeChecker_Cfg.compress_uvars =
                                 (uu___289_9489.FStar_TypeChecker_Cfg.compress_uvars);
                               FStar_TypeChecker_Cfg.no_full_norm = true;
                               FStar_TypeChecker_Cfg.check_no_uvars =
                                 (uu___289_9489.FStar_TypeChecker_Cfg.check_no_uvars);
                               FStar_TypeChecker_Cfg.unmeta = false;
                               FStar_TypeChecker_Cfg.unascribe = false;
                               FStar_TypeChecker_Cfg.in_full_norm_request =
                                 (uu___289_9489.FStar_TypeChecker_Cfg.in_full_norm_request);
                               FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                 =
                                 (uu___289_9489.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                               FStar_TypeChecker_Cfg.nbe_step =
                                 (uu___289_9489.FStar_TypeChecker_Cfg.nbe_step)
                             }  in
                           let cfg' =
                             let uu___290_9491 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps = steps';
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___290_9491.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___290_9491.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 [FStar_TypeChecker_Env.NoDelta];
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___290_9491.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong =
                                 (uu___290_9491.FStar_TypeChecker_Cfg.strong);
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___290_9491.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___290_9491.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___290_9491.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____9493 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9493 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9525  -> dummy :: env1) env)
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
                                          let uu____9566 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9566)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___291_9573 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___291_9573.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___291_9573.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9574 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9580  ->
                                 let uu____9581 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9581);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___292_9590 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___292_9590.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___292_9590.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___292_9590.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___292_9590.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___292_9590.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___292_9590.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___292_9590.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___292_9590.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____9593)::uu____9594 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 =
                        if
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.in_full_norm_request
                        then closure_as_term cfg env t1
                        else
                          (let steps' =
                             let uu___289_9612 =
                               cfg.FStar_TypeChecker_Cfg.steps  in
                             {
                               FStar_TypeChecker_Cfg.beta =
                                 (uu___289_9612.FStar_TypeChecker_Cfg.beta);
                               FStar_TypeChecker_Cfg.iota = false;
                               FStar_TypeChecker_Cfg.zeta = false;
                               FStar_TypeChecker_Cfg.weak = false;
                               FStar_TypeChecker_Cfg.hnf =
                                 (uu___289_9612.FStar_TypeChecker_Cfg.hnf);
                               FStar_TypeChecker_Cfg.primops = false;
                               FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                 = true;
                               FStar_TypeChecker_Cfg.unfold_until =
                                 (uu___289_9612.FStar_TypeChecker_Cfg.unfold_until);
                               FStar_TypeChecker_Cfg.unfold_only =
                                 (uu___289_9612.FStar_TypeChecker_Cfg.unfold_only);
                               FStar_TypeChecker_Cfg.unfold_fully =
                                 (uu___289_9612.FStar_TypeChecker_Cfg.unfold_fully);
                               FStar_TypeChecker_Cfg.unfold_attr =
                                 (uu___289_9612.FStar_TypeChecker_Cfg.unfold_attr);
                               FStar_TypeChecker_Cfg.unfold_tac =
                                 (uu___289_9612.FStar_TypeChecker_Cfg.unfold_tac);
                               FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                 = false;
                               FStar_TypeChecker_Cfg.simplify = false;
                               FStar_TypeChecker_Cfg.erase_universes =
                                 (uu___289_9612.FStar_TypeChecker_Cfg.erase_universes);
                               FStar_TypeChecker_Cfg.allow_unbound_universes
                                 =
                                 (uu___289_9612.FStar_TypeChecker_Cfg.allow_unbound_universes);
                               FStar_TypeChecker_Cfg.reify_ = false;
                               FStar_TypeChecker_Cfg.compress_uvars =
                                 (uu___289_9612.FStar_TypeChecker_Cfg.compress_uvars);
                               FStar_TypeChecker_Cfg.no_full_norm = true;
                               FStar_TypeChecker_Cfg.check_no_uvars =
                                 (uu___289_9612.FStar_TypeChecker_Cfg.check_no_uvars);
                               FStar_TypeChecker_Cfg.unmeta = false;
                               FStar_TypeChecker_Cfg.unascribe = false;
                               FStar_TypeChecker_Cfg.in_full_norm_request =
                                 (uu___289_9612.FStar_TypeChecker_Cfg.in_full_norm_request);
                               FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                 =
                                 (uu___289_9612.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                               FStar_TypeChecker_Cfg.nbe_step =
                                 (uu___289_9612.FStar_TypeChecker_Cfg.nbe_step)
                             }  in
                           let cfg' =
                             let uu___290_9614 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps = steps';
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___290_9614.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___290_9614.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 [FStar_TypeChecker_Env.NoDelta];
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___290_9614.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong =
                                 (uu___290_9614.FStar_TypeChecker_Cfg.strong);
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___290_9614.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___290_9614.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___290_9614.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           norm cfg' env [] t1)
                         in
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
                                     fun uu____9648  -> dummy :: env1) env)
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
                                          let uu____9689 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9689)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___291_9696 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___291_9696.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___291_9696.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9697 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9703  ->
                                 let uu____9704 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9704);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___292_9713 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___292_9713.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___292_9713.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___292_9713.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___292_9713.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___292_9713.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___292_9713.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___292_9713.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___292_9713.FStar_TypeChecker_Cfg.reifying)
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
                             let uu___289_9719 =
                               cfg.FStar_TypeChecker_Cfg.steps  in
                             {
                               FStar_TypeChecker_Cfg.beta =
                                 (uu___289_9719.FStar_TypeChecker_Cfg.beta);
                               FStar_TypeChecker_Cfg.iota = false;
                               FStar_TypeChecker_Cfg.zeta = false;
                               FStar_TypeChecker_Cfg.weak = false;
                               FStar_TypeChecker_Cfg.hnf =
                                 (uu___289_9719.FStar_TypeChecker_Cfg.hnf);
                               FStar_TypeChecker_Cfg.primops = false;
                               FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                 = true;
                               FStar_TypeChecker_Cfg.unfold_until =
                                 (uu___289_9719.FStar_TypeChecker_Cfg.unfold_until);
                               FStar_TypeChecker_Cfg.unfold_only =
                                 (uu___289_9719.FStar_TypeChecker_Cfg.unfold_only);
                               FStar_TypeChecker_Cfg.unfold_fully =
                                 (uu___289_9719.FStar_TypeChecker_Cfg.unfold_fully);
                               FStar_TypeChecker_Cfg.unfold_attr =
                                 (uu___289_9719.FStar_TypeChecker_Cfg.unfold_attr);
                               FStar_TypeChecker_Cfg.unfold_tac =
                                 (uu___289_9719.FStar_TypeChecker_Cfg.unfold_tac);
                               FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                 = false;
                               FStar_TypeChecker_Cfg.simplify = false;
                               FStar_TypeChecker_Cfg.erase_universes =
                                 (uu___289_9719.FStar_TypeChecker_Cfg.erase_universes);
                               FStar_TypeChecker_Cfg.allow_unbound_universes
                                 =
                                 (uu___289_9719.FStar_TypeChecker_Cfg.allow_unbound_universes);
                               FStar_TypeChecker_Cfg.reify_ = false;
                               FStar_TypeChecker_Cfg.compress_uvars =
                                 (uu___289_9719.FStar_TypeChecker_Cfg.compress_uvars);
                               FStar_TypeChecker_Cfg.no_full_norm = true;
                               FStar_TypeChecker_Cfg.check_no_uvars =
                                 (uu___289_9719.FStar_TypeChecker_Cfg.check_no_uvars);
                               FStar_TypeChecker_Cfg.unmeta = false;
                               FStar_TypeChecker_Cfg.unascribe = false;
                               FStar_TypeChecker_Cfg.in_full_norm_request =
                                 (uu___289_9719.FStar_TypeChecker_Cfg.in_full_norm_request);
                               FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                 =
                                 (uu___289_9719.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                               FStar_TypeChecker_Cfg.nbe_step =
                                 (uu___289_9719.FStar_TypeChecker_Cfg.nbe_step)
                             }  in
                           let cfg' =
                             let uu___290_9721 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps = steps';
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___290_9721.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___290_9721.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 [FStar_TypeChecker_Env.NoDelta];
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___290_9721.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong =
                                 (uu___290_9721.FStar_TypeChecker_Cfg.strong);
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___290_9721.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___290_9721.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___290_9721.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           norm cfg' env [] t1)
                         in
                      rebuild cfg env stack t2
                    else
                      (let uu____9723 = FStar_Syntax_Subst.open_term' bs body
                          in
                       match uu____9723 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____9755  -> dummy :: env1) env)
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
                                          let uu____9796 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____9796)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___291_9803 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___291_9803.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___291_9803.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____9804 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____9810  ->
                                 let uu____9811 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____9811);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___292_9820 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___292_9820.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___292_9820.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___292_9820.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___292_9820.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___292_9820.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___292_9820.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___292_9820.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___292_9820.FStar_TypeChecker_Cfg.reifying)
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
                      (fun uu____9859  ->
                         fun stack1  ->
                           match uu____9859 with
                           | (a,aq) ->
                               let uu____9871 =
                                 let uu____9872 =
                                   let uu____9879 =
                                     let uu____9880 =
                                       let uu____9911 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____9911, false)  in
                                     Clos uu____9880  in
                                   (uu____9879, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____9872  in
                               uu____9871 :: stack1) args)
                  in
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____9999  ->
                     let uu____10000 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____10000);
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
                             ((let uu___293_10046 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___293_10046.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___293_10046.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____10047 ->
                      let uu____10062 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____10062)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____10065 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____10065 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____10090 =
                          let uu____10091 =
                            let uu____10098 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___294_10104 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___294_10104.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___294_10104.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____10098)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____10091  in
                        mk uu____10090 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____10123 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____10123
               else
                 (let uu____10125 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____10125 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____10133 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____10155  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____10133 c1  in
                      let t2 =
                        let uu____10177 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____10177 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____10288)::uu____10289 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10302  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____10303)::uu____10304 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10315  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____10316,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____10317;
                                   FStar_Syntax_Syntax.vars = uu____10318;_},uu____10319,uu____10320))::uu____10321
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10328  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____10329)::uu____10330 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10341  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____10342 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10345  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____10349  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____10374 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____10374
                         | FStar_Util.Inr c ->
                             let uu____10388 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____10388
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____10411 =
                               let uu____10412 =
                                 let uu____10439 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____10439, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____10412
                                in
                             mk uu____10411 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____10474 ->
                           let uu____10475 =
                             let uu____10476 =
                               let uu____10477 =
                                 let uu____10504 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____10504, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____10477
                                in
                             mk uu____10476 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____10475))))
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
                   let uu___295_10581 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___296_10584 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___296_10584.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___296_10584.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___296_10584.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___296_10584.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___296_10584.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___296_10584.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___296_10584.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___296_10584.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___296_10584.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___296_10584.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___296_10584.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___296_10584.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___296_10584.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___296_10584.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___296_10584.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___296_10584.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___296_10584.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___296_10584.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___296_10584.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___296_10584.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___296_10584.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___296_10584.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___296_10584.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___296_10584.FStar_TypeChecker_Cfg.nbe_step)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___295_10581.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___295_10581.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___295_10581.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___295_10581.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___295_10581.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___295_10581.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___295_10581.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___295_10581.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____10620 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____10620 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___297_10640 = cfg  in
                               let uu____10641 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___297_10640.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____10641;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___297_10640.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___297_10640.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___297_10640.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___297_10640.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___297_10640.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___297_10640.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___297_10640.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____10648 =
                                 let uu____10649 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____10649  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____10648
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___298_10652 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___298_10652.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___298_10652.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___298_10652.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___298_10652.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____10653 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____10653
           | FStar_Syntax_Syntax.Tm_let
               ((uu____10664,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____10665;
                               FStar_Syntax_Syntax.lbunivs = uu____10666;
                               FStar_Syntax_Syntax.lbtyp = uu____10667;
                               FStar_Syntax_Syntax.lbeff = uu____10668;
                               FStar_Syntax_Syntax.lbdef = uu____10669;
                               FStar_Syntax_Syntax.lbattrs = uu____10670;
                               FStar_Syntax_Syntax.lbpos = uu____10671;_}::uu____10672),uu____10673)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name
                   cfg.FStar_TypeChecker_Cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____10713 =
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
               if uu____10713
               then
                 let binder =
                   let uu____10715 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____10715  in
                 let env1 =
                   let uu____10725 =
                     let uu____10732 =
                       let uu____10733 =
                         let uu____10764 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____10764,
                           false)
                          in
                       Clos uu____10733  in
                     ((FStar_Pervasives_Native.Some binder), uu____10732)  in
                   uu____10725 :: env  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____10859  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                 then
                   (FStar_TypeChecker_Cfg.log cfg
                      (fun uu____10863  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____10864 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____10864))
                 else
                   (let uu____10866 =
                      let uu____10871 =
                        let uu____10872 =
                          let uu____10877 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____10877
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____10872]  in
                      FStar_Syntax_Subst.open_term uu____10871 body  in
                    match uu____10866 with
                    | (bs,body1) ->
                        (FStar_TypeChecker_Cfg.log cfg
                           (fun uu____10898  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____10906 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____10906  in
                            FStar_Util.Inl
                              (let uu___299_10916 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___299_10916.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___299_10916.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____10919  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___300_10921 = lb  in
                             let uu____10922 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___300_10921.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___300_10921.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____10922;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___300_10921.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___300_10921.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10947  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___301_10970 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps =
                                 (uu___301_10970.FStar_TypeChecker_Cfg.steps);
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___301_10970.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___301_10970.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 (uu___301_10970.FStar_TypeChecker_Cfg.delta_level);
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___301_10970.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong = true;
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___301_10970.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___301_10970.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___301_10970.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           FStar_TypeChecker_Cfg.log cfg1
                             (fun uu____10973  ->
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
               let uu____10990 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____10990 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____11026 =
                               let uu___302_11027 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___302_11027.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___302_11027.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____11026  in
                           let uu____11028 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____11028 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____11054 =
                                   FStar_List.map (fun uu____11070  -> dummy)
                                     lbs1
                                    in
                                 let uu____11071 =
                                   let uu____11080 =
                                     FStar_List.map
                                       (fun uu____11100  -> dummy) xs1
                                      in
                                   FStar_List.append uu____11080 env  in
                                 FStar_List.append uu____11054 uu____11071
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____11124 =
                                       let uu___303_11125 = rc  in
                                       let uu____11126 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___303_11125.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____11126;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___303_11125.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____11124
                                 | uu____11135 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___304_11141 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___304_11141.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___304_11141.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___304_11141.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___304_11141.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____11151 =
                        FStar_List.map (fun uu____11167  -> dummy) lbs2  in
                      FStar_List.append uu____11151 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____11175 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____11175 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___305_11191 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___305_11191.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___305_11191.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
               ->
               let uu____11220 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____11220
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____11239 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____11315  ->
                        match uu____11315 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___306_11436 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___306_11436.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___306_11436.FStar_Syntax_Syntax.sort)
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
               (match uu____11239 with
                | (rec_env,memos,uu____11663) ->
                    let uu____11716 =
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
                             let uu____12039 =
                               let uu____12046 =
                                 let uu____12047 =
                                   let uu____12078 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____12078, false)
                                    in
                                 Clos uu____12047  in
                               (FStar_Pervasives_Native.None, uu____12046)
                                in
                             uu____12039 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____12182  ->
                     let uu____12183 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____12183);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____12205 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____12207::uu____12208 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____12213) ->
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
                             | uu____12236 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____12250 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____12250
                              | uu____12261 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____12267 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____12291 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____12305 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____12318 =
                        let uu____12319 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____12320 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____12319 uu____12320
                         in
                      failwith uu____12318
                    else
                      (let uu____12322 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____12322)
                | uu____12323 -> norm cfg env stack t2))

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
              let uu____12332 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____12332 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____12346  ->
                        let uu____12347 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____12347);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____12358  ->
                        let uu____12359 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____12360 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____12359 uu____12360);
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
                      | (UnivArgs (us',uu____12373))::stack1 ->
                          ((let uu____12382 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____12382
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____12386 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____12386) us'
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
                      | uu____12419 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____12422 ->
                          let uu____12425 =
                            let uu____12426 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____12426
                             in
                          failwith uu____12425
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
                  let uu___307_12450 = cfg  in
                  let uu____12451 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____12451;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___307_12450.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___307_12450.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___307_12450.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___307_12450.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___307_12450.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___307_12450.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___307_12450.FStar_TypeChecker_Cfg.reifying)
                  }
                else
                  (let uu___308_12453 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___309_12456 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___309_12456.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___309_12456.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta = false;
                          FStar_TypeChecker_Cfg.weak =
                            (uu___309_12456.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___309_12456.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___309_12456.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___309_12456.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___309_12456.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___309_12456.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___309_12456.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___309_12456.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___309_12456.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___309_12456.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___309_12456.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___309_12456.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___309_12456.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___309_12456.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___309_12456.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___309_12456.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___309_12456.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___309_12456.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___309_12456.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___309_12456.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___309_12456.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___309_12456.FStar_TypeChecker_Cfg.nbe_step)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___308_12453.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___308_12453.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___308_12453.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___308_12453.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___308_12453.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___308_12453.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___308_12453.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___308_12453.FStar_TypeChecker_Cfg.reifying)
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
                  (fun uu____12490  ->
                     let uu____12491 = FStar_Syntax_Print.tag_of_term head2
                        in
                     let uu____12492 =
                       FStar_Syntax_Print.term_to_string head2  in
                     FStar_Util.print2 "Reifying: (%s) %s\n" uu____12491
                       uu____12492);
                (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                 let uu____12494 =
                   let uu____12495 = FStar_Syntax_Subst.compress head3  in
                   uu____12495.FStar_Syntax_Syntax.n  in
                 match uu____12494 with
                 | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                     let ed =
                       let uu____12513 =
                         FStar_TypeChecker_Env.norm_eff_name
                           cfg.FStar_TypeChecker_Cfg.tcenv m
                          in
                       FStar_TypeChecker_Env.get_effect_decl
                         cfg.FStar_TypeChecker_Cfg.tcenv uu____12513
                        in
                     let uu____12514 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____12514 with
                      | (uu____12515,bind_repr) ->
                          (match lb.FStar_Syntax_Syntax.lbname with
                           | FStar_Util.Inr uu____12525 ->
                               failwith
                                 "Cannot reify a top-level let binding"
                           | FStar_Util.Inl x ->
                               let is_return e =
                                 let uu____12535 =
                                   let uu____12536 =
                                     FStar_Syntax_Subst.compress e  in
                                   uu____12536.FStar_Syntax_Syntax.n  in
                                 match uu____12535 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e1,FStar_Syntax_Syntax.Meta_monadic
                                      (uu____12542,uu____12543))
                                     ->
                                     let uu____12552 =
                                       let uu____12553 =
                                         FStar_Syntax_Subst.compress e1  in
                                       uu____12553.FStar_Syntax_Syntax.n  in
                                     (match uu____12552 with
                                      | FStar_Syntax_Syntax.Tm_meta
                                          (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                           (uu____12559,msrc,uu____12561))
                                          when
                                          FStar_Syntax_Util.is_pure_effect
                                            msrc
                                          ->
                                          let uu____12570 =
                                            FStar_Syntax_Subst.compress e2
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____12570
                                      | uu____12571 ->
                                          FStar_Pervasives_Native.None)
                                 | uu____12572 ->
                                     FStar_Pervasives_Native.None
                                  in
                               let uu____12573 =
                                 is_return lb.FStar_Syntax_Syntax.lbdef  in
                               (match uu____12573 with
                                | FStar_Pervasives_Native.Some e ->
                                    let lb1 =
                                      let uu___310_12578 = lb  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          (uu___310_12578.FStar_Syntax_Syntax.lbname);
                                        FStar_Syntax_Syntax.lbunivs =
                                          (uu___310_12578.FStar_Syntax_Syntax.lbunivs);
                                        FStar_Syntax_Syntax.lbtyp =
                                          (uu___310_12578.FStar_Syntax_Syntax.lbtyp);
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_PURE_lid;
                                        FStar_Syntax_Syntax.lbdef = e;
                                        FStar_Syntax_Syntax.lbattrs =
                                          (uu___310_12578.FStar_Syntax_Syntax.lbattrs);
                                        FStar_Syntax_Syntax.lbpos =
                                          (uu___310_12578.FStar_Syntax_Syntax.lbpos)
                                      }  in
                                    let uu____12579 = FStar_List.tl stack  in
                                    let uu____12580 =
                                      let uu____12581 =
                                        let uu____12588 =
                                          let uu____12589 =
                                            let uu____12602 =
                                              FStar_Syntax_Util.mk_reify body
                                               in
                                            ((false, [lb1]), uu____12602)  in
                                          FStar_Syntax_Syntax.Tm_let
                                            uu____12589
                                           in
                                        FStar_Syntax_Syntax.mk uu____12588
                                         in
                                      uu____12581
                                        FStar_Pervasives_Native.None
                                        head3.FStar_Syntax_Syntax.pos
                                       in
                                    norm cfg env uu____12579 uu____12580
                                | FStar_Pervasives_Native.None  ->
                                    let uu____12618 =
                                      let uu____12619 = is_return body  in
                                      match uu____12619 with
                                      | FStar_Pervasives_Native.Some
                                          {
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_bvar y;
                                            FStar_Syntax_Syntax.pos =
                                              uu____12623;
                                            FStar_Syntax_Syntax.vars =
                                              uu____12624;_}
                                          -> FStar_Syntax_Syntax.bv_eq x y
                                      | uu____12627 -> false  in
                                    if uu____12618
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
                                         let uu____12648 =
                                           let uu____12655 =
                                             let uu____12656 =
                                               let uu____12673 =
                                                 let uu____12680 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x
                                                    in
                                                 [uu____12680]  in
                                               (uu____12673, body1,
                                                 (FStar_Pervasives_Native.Some
                                                    body_rc))
                                                in
                                             FStar_Syntax_Syntax.Tm_abs
                                               uu____12656
                                              in
                                           FStar_Syntax_Syntax.mk uu____12655
                                            in
                                         uu____12648
                                           FStar_Pervasives_Native.None
                                           body1.FStar_Syntax_Syntax.pos
                                          in
                                       let close1 = closure_as_term cfg env
                                          in
                                       let bind_inst =
                                         let uu____12714 =
                                           let uu____12715 =
                                             FStar_Syntax_Subst.compress
                                               bind_repr
                                              in
                                           uu____12715.FStar_Syntax_Syntax.n
                                            in
                                         match uu____12714 with
                                         | FStar_Syntax_Syntax.Tm_uinst
                                             (bind1,uu____12721::uu____12722::[])
                                             ->
                                             let uu____12727 =
                                               let uu____12734 =
                                                 let uu____12735 =
                                                   let uu____12742 =
                                                     let uu____12743 =
                                                       let uu____12744 =
                                                         close1
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                         cfg.FStar_TypeChecker_Cfg.tcenv
                                                         uu____12744
                                                        in
                                                     let uu____12745 =
                                                       let uu____12748 =
                                                         let uu____12749 =
                                                           close1 t  in
                                                         (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                           cfg.FStar_TypeChecker_Cfg.tcenv
                                                           uu____12749
                                                          in
                                                       [uu____12748]  in
                                                     uu____12743 ::
                                                       uu____12745
                                                      in
                                                   (bind1, uu____12742)  in
                                                 FStar_Syntax_Syntax.Tm_uinst
                                                   uu____12735
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____12734
                                                in
                                             uu____12727
                                               FStar_Pervasives_Native.None
                                               rng
                                         | uu____12755 ->
                                             failwith
                                               "NIY : Reification of indexed effects"
                                          in
                                       let maybe_range_arg =
                                         let uu____12767 =
                                           FStar_Util.for_some
                                             (FStar_Syntax_Util.attr_eq
                                                FStar_Syntax_Util.dm4f_bind_range_attr)
                                             ed.FStar_Syntax_Syntax.eff_attrs
                                            in
                                         if uu____12767
                                         then
                                           let uu____12776 =
                                             let uu____12783 =
                                               FStar_Syntax_Embeddings.embed
                                                 FStar_Syntax_Embeddings.e_range
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                 lb.FStar_Syntax_Syntax.lbpos
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____12783
                                              in
                                           let uu____12784 =
                                             let uu____12793 =
                                               let uu____12800 =
                                                 FStar_Syntax_Embeddings.embed
                                                   FStar_Syntax_Embeddings.e_range
                                                   body2.FStar_Syntax_Syntax.pos
                                                   body2.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_Syntax.as_arg
                                                 uu____12800
                                                in
                                             [uu____12793]  in
                                           uu____12776 :: uu____12784
                                         else []  in
                                       let reified =
                                         let uu____12829 =
                                           let uu____12836 =
                                             let uu____12837 =
                                               let uu____12852 =
                                                 let uu____12861 =
                                                   let uu____12870 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       lb.FStar_Syntax_Syntax.lbtyp
                                                      in
                                                   let uu____12877 =
                                                     let uu____12886 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         t
                                                        in
                                                     [uu____12886]  in
                                                   uu____12870 :: uu____12877
                                                    in
                                                 let uu____12911 =
                                                   let uu____12920 =
                                                     let uu____12929 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         FStar_Syntax_Syntax.tun
                                                        in
                                                     let uu____12936 =
                                                       let uu____12945 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           head4
                                                          in
                                                       let uu____12952 =
                                                         let uu____12961 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             FStar_Syntax_Syntax.tun
                                                            in
                                                         let uu____12968 =
                                                           let uu____12977 =
                                                             FStar_Syntax_Syntax.as_arg
                                                               body2
                                                              in
                                                           [uu____12977]  in
                                                         uu____12961 ::
                                                           uu____12968
                                                          in
                                                       uu____12945 ::
                                                         uu____12952
                                                        in
                                                     uu____12929 ::
                                                       uu____12936
                                                      in
                                                   FStar_List.append
                                                     maybe_range_arg
                                                     uu____12920
                                                    in
                                                 FStar_List.append
                                                   uu____12861 uu____12911
                                                  in
                                               (bind_inst, uu____12852)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____12837
                                              in
                                           FStar_Syntax_Syntax.mk uu____12836
                                            in
                                         uu____12829
                                           FStar_Pervasives_Native.None rng
                                          in
                                       FStar_TypeChecker_Cfg.log cfg
                                         (fun uu____13043  ->
                                            let uu____13044 =
                                              FStar_Syntax_Print.term_to_string
                                                head0
                                               in
                                            let uu____13045 =
                                              FStar_Syntax_Print.term_to_string
                                                reified
                                               in
                                            FStar_Util.print2
                                              "Reified (1) <%s> to %s\n"
                                              uu____13044 uu____13045);
                                       (let uu____13046 = FStar_List.tl stack
                                           in
                                        norm cfg env uu____13046 reified)))))
                 | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                     let ed =
                       let uu____13070 =
                         FStar_TypeChecker_Env.norm_eff_name
                           cfg.FStar_TypeChecker_Cfg.tcenv m
                          in
                       FStar_TypeChecker_Env.get_effect_decl
                         cfg.FStar_TypeChecker_Cfg.tcenv uu____13070
                        in
                     let uu____13071 = ed.FStar_Syntax_Syntax.bind_repr  in
                     (match uu____13071 with
                      | (uu____13072,bind_repr) ->
                          let maybe_unfold_action head4 =
                            let maybe_extract_fv t1 =
                              let t2 =
                                let uu____13109 =
                                  let uu____13110 =
                                    FStar_Syntax_Subst.compress t1  in
                                  uu____13110.FStar_Syntax_Syntax.n  in
                                match uu____13109 with
                                | FStar_Syntax_Syntax.Tm_uinst
                                    (t2,uu____13114) -> t2
                                | uu____13119 -> head4  in
                              let uu____13120 =
                                let uu____13121 =
                                  FStar_Syntax_Subst.compress t2  in
                                uu____13121.FStar_Syntax_Syntax.n  in
                              match uu____13120 with
                              | FStar_Syntax_Syntax.Tm_fvar x ->
                                  FStar_Pervasives_Native.Some x
                              | uu____13127 -> FStar_Pervasives_Native.None
                               in
                            let uu____13128 = maybe_extract_fv head4  in
                            match uu____13128 with
                            | FStar_Pervasives_Native.Some x when
                                let uu____13138 =
                                  FStar_Syntax_Syntax.lid_of_fv x  in
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv uu____13138
                                ->
                                let head5 = norm cfg env [] head4  in
                                let action_unfolded =
                                  let uu____13143 = maybe_extract_fv head5
                                     in
                                  match uu____13143 with
                                  | FStar_Pervasives_Native.Some uu____13148
                                      -> FStar_Pervasives_Native.Some true
                                  | uu____13149 ->
                                      FStar_Pervasives_Native.Some false
                                   in
                                (head5, action_unfolded)
                            | uu____13154 ->
                                (head4, FStar_Pervasives_Native.None)
                             in
                          ((let is_arg_impure uu____13169 =
                              match uu____13169 with
                              | (e,q) ->
                                  let uu____13176 =
                                    let uu____13177 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____13177.FStar_Syntax_Syntax.n  in
                                  (match uu____13176 with
                                   | FStar_Syntax_Syntax.Tm_meta
                                       (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                        (m1,m2,t'))
                                       ->
                                       let uu____13192 =
                                         FStar_Syntax_Util.is_pure_effect m1
                                          in
                                       Prims.op_Negation uu____13192
                                   | uu____13193 -> false)
                               in
                            let uu____13194 =
                              let uu____13195 =
                                let uu____13204 =
                                  FStar_Syntax_Syntax.as_arg head_app  in
                                uu____13204 :: args  in
                              FStar_Util.for_some is_arg_impure uu____13195
                               in
                            if uu____13194
                            then
                              let uu____13223 =
                                let uu____13224 =
                                  FStar_Syntax_Print.term_to_string head3  in
                                FStar_Util.format1
                                  "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                  uu____13224
                                 in
                              failwith uu____13223
                            else ());
                           (let uu____13226 = maybe_unfold_action head_app
                               in
                            match uu____13226 with
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
                                   (fun uu____13269  ->
                                      let uu____13270 =
                                        FStar_Syntax_Print.term_to_string
                                          head0
                                         in
                                      let uu____13271 =
                                        FStar_Syntax_Print.term_to_string
                                          body1
                                         in
                                      FStar_Util.print2
                                        "Reified (2) <%s> to %s\n"
                                        uu____13270 uu____13271);
                                 (let uu____13272 = FStar_List.tl stack  in
                                  norm cfg env uu____13272 body1)))))
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic uu____13274) ->
                     do_reify_monadic fallback cfg env stack e m t
                 | FStar_Syntax_Syntax.Tm_meta
                     (e,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,t'))
                     ->
                     let lifted =
                       let uu____13298 = closure_as_term cfg env t'  in
                       reify_lift cfg e msrc mtgt uu____13298  in
                     (FStar_TypeChecker_Cfg.log cfg
                        (fun uu____13302  ->
                           let uu____13303 =
                             FStar_Syntax_Print.term_to_string lifted  in
                           FStar_Util.print1 "Reified lift to (2): %s\n"
                             uu____13303);
                      (let uu____13304 = FStar_List.tl stack  in
                       norm cfg env uu____13304 lifted))
                 | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                     let branches1 =
                       FStar_All.pipe_right branches
                         (FStar_List.map
                            (fun uu____13425  ->
                               match uu____13425 with
                               | (pat,wopt,tm) ->
                                   let uu____13473 =
                                     FStar_Syntax_Util.mk_reify tm  in
                                   (pat, wopt, uu____13473)))
                        in
                     let tm =
                       mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                         head3.FStar_Syntax_Syntax.pos
                        in
                     let uu____13505 = FStar_List.tl stack  in
                     norm cfg env uu____13505 tm
                 | uu____13506 -> fallback ())

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
              (fun uu____13520  ->
                 let uu____13521 = FStar_Ident.string_of_lid msrc  in
                 let uu____13522 = FStar_Ident.string_of_lid mtgt  in
                 let uu____13523 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____13521
                   uu____13522 uu____13523);
            (let uu____13524 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____13524
             then
               let ed =
                 let uu____13526 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____13526  in
               let uu____13527 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____13527 with
               | (uu____13528,return_repr) ->
                   let return_inst =
                     let uu____13541 =
                       let uu____13542 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____13542.FStar_Syntax_Syntax.n  in
                     match uu____13541 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____13548::[]) ->
                         let uu____13553 =
                           let uu____13560 =
                             let uu____13561 =
                               let uu____13568 =
                                 let uu____13569 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____13569]  in
                               (return_tm, uu____13568)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____13561  in
                           FStar_Syntax_Syntax.mk uu____13560  in
                         uu____13553 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____13575 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____13578 =
                     let uu____13585 =
                       let uu____13586 =
                         let uu____13601 =
                           let uu____13610 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____13617 =
                             let uu____13626 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____13626]  in
                           uu____13610 :: uu____13617  in
                         (return_inst, uu____13601)  in
                       FStar_Syntax_Syntax.Tm_app uu____13586  in
                     FStar_Syntax_Syntax.mk uu____13585  in
                   uu____13578 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____13665 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____13665 with
                | FStar_Pervasives_Native.None  ->
                    let uu____13668 =
                      let uu____13669 = FStar_Ident.text_of_lid msrc  in
                      let uu____13670 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____13669 uu____13670
                       in
                    failwith uu____13668
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____13671;
                      FStar_TypeChecker_Env.mtarget = uu____13672;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____13673;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____13695 =
                      let uu____13696 = FStar_Ident.text_of_lid msrc  in
                      let uu____13697 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____13696 uu____13697
                       in
                    failwith uu____13695
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____13698;
                      FStar_TypeChecker_Env.mtarget = uu____13699;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____13700;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____13735 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____13736 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____13735 t FStar_Syntax_Syntax.tun uu____13736))

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
                (fun uu____13792  ->
                   match uu____13792 with
                   | (a,imp) ->
                       let uu____13803 = norm cfg env [] a  in
                       (uu____13803, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____13811  ->
             let uu____13812 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____13813 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____13812 uu____13813);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____13837 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_18  -> FStar_Pervasives_Native.Some _0_18)
                     uu____13837
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___311_13840 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___311_13840.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___311_13840.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____13862 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____13862
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___312_13865 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___312_13865.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___312_13865.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____13902  ->
                      match uu____13902 with
                      | (a,i) ->
                          let uu____13913 = norm cfg env [] a  in
                          (uu____13913, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags1 =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___253_13931  ->
                       match uu___253_13931 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____13935 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____13935
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___313_13943 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___314_13946 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___314_13946.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags1
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___313_13943.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___313_13943.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun uu____13949  ->
        match uu____13949 with
        | (x,imp) ->
            let uu____13952 =
              let uu___315_13953 = x  in
              let uu____13954 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___315_13953.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___315_13953.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____13954
              }  in
            (uu____13952, imp)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____13960 =
          FStar_List.fold_left
            (fun uu____13994  ->
               fun b  ->
                 match uu____13994 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____13960 with | (nbs,uu____14074) -> FStar_List.rev nbs

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
            let uu____14106 =
              let uu___316_14107 = rc  in
              let uu____14108 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___316_14107.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____14108;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___316_14107.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____14106
        | uu____14117 -> lopt

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
            (let uu____14138 = FStar_Syntax_Print.term_to_string tm  in
             let uu____14139 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____14138 uu____14139)
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
          let uu____14161 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____14161
          then tm1
          else
            (let w t =
               let uu___317_14175 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___317_14175.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___317_14175.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____14186 =
                 let uu____14187 = FStar_Syntax_Util.unmeta t  in
                 uu____14187.FStar_Syntax_Syntax.n  in
               match uu____14186 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____14194 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____14243)::args1,(bv,uu____14246)::bs1) ->
                   let uu____14280 =
                     let uu____14281 = FStar_Syntax_Subst.compress t  in
                     uu____14281.FStar_Syntax_Syntax.n  in
                   (match uu____14280 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____14285 -> false)
               | ([],[]) -> true
               | (uu____14306,uu____14307) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____14348 = FStar_Syntax_Print.term_to_string t  in
                  let uu____14349 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____14348
                    uu____14349)
               else ();
               (let uu____14351 = FStar_Syntax_Util.head_and_args' t  in
                match uu____14351 with
                | (hd1,args) ->
                    let uu____14384 =
                      let uu____14385 = FStar_Syntax_Subst.compress hd1  in
                      uu____14385.FStar_Syntax_Syntax.n  in
                    (match uu____14384 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____14392 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____14393 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____14394 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____14392 uu____14393 uu____14394)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____14396 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____14413 = FStar_Syntax_Print.term_to_string t  in
                  let uu____14414 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____14413
                    uu____14414)
               else ();
               (let uu____14416 = FStar_Syntax_Util.is_squash t  in
                match uu____14416 with
                | FStar_Pervasives_Native.Some (uu____14427,t') ->
                    is_applied bs t'
                | uu____14439 ->
                    let uu____14448 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____14448 with
                     | FStar_Pervasives_Native.Some (uu____14459,t') ->
                         is_applied bs t'
                     | uu____14471 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____14495 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____14495 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____14502)::(q,uu____14504)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____14532 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____14533 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____14532 uu____14533)
                    else ();
                    (let uu____14535 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____14535 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____14540 =
                           let uu____14541 = FStar_Syntax_Subst.compress p
                              in
                           uu____14541.FStar_Syntax_Syntax.n  in
                         (match uu____14540 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____14549 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____14549))
                          | uu____14552 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____14555)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____14572 =
                           let uu____14573 = FStar_Syntax_Subst.compress p1
                              in
                           uu____14573.FStar_Syntax_Syntax.n  in
                         (match uu____14572 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____14581 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____14581))
                          | uu____14584 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____14588 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____14588 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____14593 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____14593 with
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
                                     let uu____14604 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____14604))
                               | uu____14607 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____14612)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____14629 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____14629 with
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
                                     let uu____14640 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____14640))
                               | uu____14643 -> FStar_Pervasives_Native.None)
                          | uu____14646 -> FStar_Pervasives_Native.None)
                     | uu____14649 -> FStar_Pervasives_Native.None))
               | uu____14652 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____14665 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____14665 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____14671)::[],uu____14672,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____14683 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____14684 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____14683
                         uu____14684)
                    else ();
                    is_quantified_const bv phi')
               | uu____14686 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____14699 =
                 let uu____14700 = FStar_Syntax_Subst.compress phi  in
                 uu____14700.FStar_Syntax_Syntax.n  in
               match uu____14699 with
               | FStar_Syntax_Syntax.Tm_match (uu____14705,br::brs) ->
                   let uu____14772 = br  in
                   (match uu____14772 with
                    | (uu____14789,uu____14790,e) ->
                        let r =
                          let uu____14811 = simp_t e  in
                          match uu____14811 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____14817 =
                                FStar_List.for_all
                                  (fun uu____14835  ->
                                     match uu____14835 with
                                     | (uu____14848,uu____14849,e') ->
                                         let uu____14863 = simp_t e'  in
                                         uu____14863 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____14817
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____14871 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____14880 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____14880
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____14911 =
                 match uu____14911 with
                 | (t1,q) ->
                     let uu____14924 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____14924 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____14952 -> (t1, q))
                  in
               let uu____14963 = FStar_Syntax_Util.head_and_args t  in
               match uu____14963 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____15029 =
                 let uu____15030 = FStar_Syntax_Util.unmeta ty  in
                 uu____15030.FStar_Syntax_Syntax.n  in
               match uu____15029 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____15034) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____15039,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____15059 -> false  in
             let simplify1 arg =
               let uu____15084 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____15084, arg)  in
             let uu____15093 = is_forall_const tm1  in
             match uu____15093 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____15098 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____15099 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____15098
                       uu____15099)
                  else ();
                  (let uu____15101 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____15101))
             | FStar_Pervasives_Native.None  ->
                 let uu____15102 =
                   let uu____15103 = FStar_Syntax_Subst.compress tm1  in
                   uu____15103.FStar_Syntax_Syntax.n  in
                 (match uu____15102 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____15107;
                              FStar_Syntax_Syntax.vars = uu____15108;_},uu____15109);
                         FStar_Syntax_Syntax.pos = uu____15110;
                         FStar_Syntax_Syntax.vars = uu____15111;_},args)
                      ->
                      let uu____15137 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____15137
                      then
                        let uu____15138 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____15138 with
                         | (FStar_Pervasives_Native.Some (true ),uu____15183)::
                             (uu____15184,(arg,uu____15186))::[] ->
                             maybe_auto_squash arg
                         | (uu____15235,(arg,uu____15237))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____15238)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____15287)::uu____15288::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____15339::(FStar_Pervasives_Native.Some (false
                                         ),uu____15340)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____15391 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____15405 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____15405
                         then
                           let uu____15406 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____15406 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____15451)::uu____15452::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____15503::(FStar_Pervasives_Native.Some (true
                                           ),uu____15504)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____15555)::(uu____15556,(arg,uu____15558))::[]
                               -> maybe_auto_squash arg
                           | (uu____15607,(arg,uu____15609))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____15610)::[]
                               -> maybe_auto_squash arg
                           | uu____15659 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____15673 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____15673
                            then
                              let uu____15674 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____15674 with
                              | uu____15719::(FStar_Pervasives_Native.Some
                                              (true ),uu____15720)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____15771)::uu____15772::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____15823)::(uu____15824,(arg,uu____15826))::[]
                                  -> maybe_auto_squash arg
                              | (uu____15875,(p,uu____15877))::(uu____15878,
                                                                (q,uu____15880))::[]
                                  ->
                                  let uu____15927 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____15927
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____15929 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____15943 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____15943
                               then
                                 let uu____15944 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____15944 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____15989)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____15990)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____16041)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____16042)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16093)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____16094)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____16145)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____16146)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____16197,(arg,uu____16199))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____16200)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____16249)::(uu____16250,(arg,uu____16252))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____16301,(arg,uu____16303))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____16304)::[]
                                     ->
                                     let uu____16353 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____16353
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____16354)::(uu____16355,(arg,uu____16357))::[]
                                     ->
                                     let uu____16406 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____16406
                                 | (uu____16407,(p,uu____16409))::(uu____16410,
                                                                   (q,uu____16412))::[]
                                     ->
                                     let uu____16459 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____16459
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____16461 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____16475 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____16475
                                  then
                                    let uu____16476 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____16476 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____16521)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____16552)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____16583 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____16597 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____16597
                                     then
                                       match args with
                                       | (t,uu____16599)::[] ->
                                           let uu____16616 =
                                             let uu____16617 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____16617.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____16616 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____16620::[],body,uu____16622)
                                                ->
                                                let uu____16649 = simp_t body
                                                   in
                                                (match uu____16649 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____16652 -> tm1)
                                            | uu____16655 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____16657))::(t,uu____16659)::[]
                                           ->
                                           let uu____16686 =
                                             let uu____16687 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____16687.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____16686 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____16690::[],body,uu____16692)
                                                ->
                                                let uu____16719 = simp_t body
                                                   in
                                                (match uu____16719 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____16722 -> tm1)
                                            | uu____16725 -> tm1)
                                       | uu____16726 -> tm1
                                     else
                                       (let uu____16736 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____16736
                                        then
                                          match args with
                                          | (t,uu____16738)::[] ->
                                              let uu____16755 =
                                                let uu____16756 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____16756.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____16755 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____16759::[],body,uu____16761)
                                                   ->
                                                   let uu____16788 =
                                                     simp_t body  in
                                                   (match uu____16788 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____16791 -> tm1)
                                               | uu____16794 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____16796))::(t,uu____16798)::[]
                                              ->
                                              let uu____16825 =
                                                let uu____16826 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____16826.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____16825 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____16829::[],body,uu____16831)
                                                   ->
                                                   let uu____16858 =
                                                     simp_t body  in
                                                   (match uu____16858 with
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
                                                    | uu____16861 -> tm1)
                                               | uu____16864 -> tm1)
                                          | uu____16865 -> tm1
                                        else
                                          (let uu____16875 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____16875
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____16876;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____16877;_},uu____16878)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____16895;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____16896;_},uu____16897)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____16914 -> tm1
                                           else
                                             (let uu____16924 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____16924 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____16944 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____16954;
                         FStar_Syntax_Syntax.vars = uu____16955;_},args)
                      ->
                      let uu____16977 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____16977
                      then
                        let uu____16978 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____16978 with
                         | (FStar_Pervasives_Native.Some (true ),uu____17023)::
                             (uu____17024,(arg,uu____17026))::[] ->
                             maybe_auto_squash arg
                         | (uu____17075,(arg,uu____17077))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____17078)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____17127)::uu____17128::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____17179::(FStar_Pervasives_Native.Some (false
                                         ),uu____17180)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____17231 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____17245 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____17245
                         then
                           let uu____17246 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____17246 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____17291)::uu____17292::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____17343::(FStar_Pervasives_Native.Some (true
                                           ),uu____17344)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____17395)::(uu____17396,(arg,uu____17398))::[]
                               -> maybe_auto_squash arg
                           | (uu____17447,(arg,uu____17449))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____17450)::[]
                               -> maybe_auto_squash arg
                           | uu____17499 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____17513 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____17513
                            then
                              let uu____17514 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____17514 with
                              | uu____17559::(FStar_Pervasives_Native.Some
                                              (true ),uu____17560)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____17611)::uu____17612::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____17663)::(uu____17664,(arg,uu____17666))::[]
                                  -> maybe_auto_squash arg
                              | (uu____17715,(p,uu____17717))::(uu____17718,
                                                                (q,uu____17720))::[]
                                  ->
                                  let uu____17767 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____17767
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____17769 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____17783 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____17783
                               then
                                 let uu____17784 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____17784 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17829)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17830)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17881)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____17882)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____17933)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____17934)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____17985)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____17986)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____18037,(arg,uu____18039))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____18040)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18089)::(uu____18090,(arg,uu____18092))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____18141,(arg,uu____18143))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____18144)::[]
                                     ->
                                     let uu____18193 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____18193
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18194)::(uu____18195,(arg,uu____18197))::[]
                                     ->
                                     let uu____18246 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____18246
                                 | (uu____18247,(p,uu____18249))::(uu____18250,
                                                                   (q,uu____18252))::[]
                                     ->
                                     let uu____18299 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____18299
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____18301 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____18315 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____18315
                                  then
                                    let uu____18316 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____18316 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____18361)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____18392)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____18423 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____18437 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____18437
                                     then
                                       match args with
                                       | (t,uu____18439)::[] ->
                                           let uu____18456 =
                                             let uu____18457 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____18457.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____18456 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____18460::[],body,uu____18462)
                                                ->
                                                let uu____18489 = simp_t body
                                                   in
                                                (match uu____18489 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____18492 -> tm1)
                                            | uu____18495 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____18497))::(t,uu____18499)::[]
                                           ->
                                           let uu____18526 =
                                             let uu____18527 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____18527.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____18526 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____18530::[],body,uu____18532)
                                                ->
                                                let uu____18559 = simp_t body
                                                   in
                                                (match uu____18559 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____18562 -> tm1)
                                            | uu____18565 -> tm1)
                                       | uu____18566 -> tm1
                                     else
                                       (let uu____18576 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____18576
                                        then
                                          match args with
                                          | (t,uu____18578)::[] ->
                                              let uu____18595 =
                                                let uu____18596 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____18596.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____18595 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____18599::[],body,uu____18601)
                                                   ->
                                                   let uu____18628 =
                                                     simp_t body  in
                                                   (match uu____18628 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____18631 -> tm1)
                                               | uu____18634 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____18636))::(t,uu____18638)::[]
                                              ->
                                              let uu____18665 =
                                                let uu____18666 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____18666.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____18665 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____18669::[],body,uu____18671)
                                                   ->
                                                   let uu____18698 =
                                                     simp_t body  in
                                                   (match uu____18698 with
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
                                                    | uu____18701 -> tm1)
                                               | uu____18704 -> tm1)
                                          | uu____18705 -> tm1
                                        else
                                          (let uu____18715 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____18715
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18716;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18717;_},uu____18718)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____18735;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____18736;_},uu____18737)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____18754 -> tm1
                                           else
                                             (let uu____18764 =
                                                FStar_Syntax_Util.is_auto_squash
                                                  tm1
                                                 in
                                              match uu____18764 with
                                              | FStar_Pervasives_Native.Some
                                                  (FStar_Syntax_Syntax.U_zero
                                                   ,t)
                                                  when
                                                  FStar_Syntax_Util.is_sub_singleton
                                                    t
                                                  -> t
                                              | uu____18784 ->
                                                  reduce_equality cfg env
                                                    stack tm1))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____18799 = simp_t t  in
                      (match uu____18799 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____18802 ->
                      let uu____18825 = is_const_match tm1  in
                      (match uu____18825 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____18828 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____18838  ->
               (let uu____18840 = FStar_Syntax_Print.tag_of_term t  in
                let uu____18841 = FStar_Syntax_Print.term_to_string t  in
                let uu____18842 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____18849 =
                  let uu____18850 =
                    let uu____18853 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____18853
                     in
                  stack_to_string uu____18850  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____18840 uu____18841 uu____18842 uu____18849);
               (let uu____18876 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____18876
                then
                  let uu____18877 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____18877 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____18884 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____18885 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____18886 =
                          let uu____18887 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____18887
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____18884
                          uu____18885 uu____18886);
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
                   let uu____18905 =
                     let uu____18906 =
                       let uu____18907 =
                         FStar_Util.time_diff time_then time_now  in
                       FStar_Pervasives_Native.snd uu____18907  in
                     FStar_Util.string_of_int uu____18906  in
                   let uu____18912 = FStar_Syntax_Print.term_to_string tm  in
                   let uu____18913 = FStar_Syntax_Print.term_to_string t1  in
                   FStar_Util.print3 "Normalized (%s ms) %s\n\tto %s\n"
                     uu____18905 uu____18912 uu____18913)
                else ();
                rebuild cfg env stack1 t1)
           | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
           | (Meta (uu____18919,m,r))::stack1 ->
               let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
               rebuild cfg env stack1 t2
           | (MemoLazy r)::stack1 ->
               (set_memo cfg r (env, t1);
                FStar_TypeChecker_Cfg.log cfg
                  (fun uu____18970  ->
                     let uu____18971 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 "\tSet memo %s\n" uu____18971);
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
               let uu____19009 =
                 let uu___318_19010 = FStar_Syntax_Util.abs bs1 t1 lopt1  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___318_19010.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = r;
                   FStar_Syntax_Syntax.vars =
                     (uu___318_19010.FStar_Syntax_Syntax.vars)
                 }  in
               rebuild cfg env stack1 uu____19009
           | (Arg (Univ uu____19013,uu____19014,uu____19015))::uu____19016 ->
               failwith "Impossible"
           | (Arg (Dummy ,uu____19019,uu____19020))::uu____19021 ->
               failwith "Impossible"
           | (UnivArgs (us,r))::stack1 ->
               let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,uu____19036,uu____19037),aq,r))::stack1
               when
               let uu____19087 = head_of t1  in
               FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____19087 ->
               let t2 =
                 let uu____19091 =
                   let uu____19096 =
                     let uu____19097 = closure_as_term cfg env_arg tm  in
                     (uu____19097, aq)  in
                   FStar_Syntax_Syntax.extend_app t1 uu____19096  in
                 uu____19091 FStar_Pervasives_Native.None r  in
               rebuild cfg env stack1 t2
           | (Arg (Clos (env_arg,tm,m,uu____19107),aq,r))::stack1 ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____19160  ->
                     let uu____19161 = FStar_Syntax_Print.term_to_string tm
                        in
                     FStar_Util.print1 "Rebuilding with arg %s\n" uu____19161);
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
                  (let uu____19173 = FStar_ST.op_Bang m  in
                   match uu____19173 with
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
                   | FStar_Pervasives_Native.Some (uu____19316,a) ->
                       let t2 =
                         FStar_Syntax_Syntax.extend_app t1 (a, aq)
                           FStar_Pervasives_Native.None r
                          in
                       rebuild cfg env_arg stack1 t2))
           | (App (env1,head1,aq,r))::stack' when should_reify cfg stack ->
               let t0 = t1  in
               let fallback msg uu____19369 =
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____19373  ->
                      let uu____19374 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print2 "Not reifying%s: %s\n" msg
                        uu____19374);
                 (let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack' t2)
                  in
               let uu____19380 =
                 let uu____19381 = FStar_Syntax_Subst.compress t1  in
                 uu____19381.FStar_Syntax_Syntax.n  in
               (match uu____19380 with
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                    do_reify_monadic (fallback " (1)") cfg env1 stack t2 m ty
                | FStar_Syntax_Syntax.Tm_meta
                    (t2,FStar_Syntax_Syntax.Meta_monadic_lift (msrc,mtgt,ty))
                    ->
                    let lifted =
                      let uu____19408 = closure_as_term cfg env1 ty  in
                      reify_lift cfg t2 msrc mtgt uu____19408  in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____19412  ->
                          let uu____19413 =
                            FStar_Syntax_Print.term_to_string lifted  in
                          FStar_Util.print1 "Reified lift to (1): %s\n"
                            uu____19413);
                     (let uu____19414 = FStar_List.tl stack  in
                      norm cfg env1 uu____19414 lifted))
                | FStar_Syntax_Syntax.Tm_app
                    ({
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reflect uu____19415);
                       FStar_Syntax_Syntax.pos = uu____19416;
                       FStar_Syntax_Syntax.vars = uu____19417;_},(e,uu____19419)::[])
                    -> norm cfg env1 stack' e
                | FStar_Syntax_Syntax.Tm_app uu____19448 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                    ->
                    let uu____19463 = FStar_Syntax_Util.head_and_args t1  in
                    (match uu____19463 with
                     | (hd1,args) ->
                         let uu____19500 =
                           let uu____19501 = FStar_Syntax_Util.un_uinst hd1
                              in
                           uu____19501.FStar_Syntax_Syntax.n  in
                         (match uu____19500 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu____19505 =
                                FStar_TypeChecker_Cfg.find_prim_step cfg fv
                                 in
                              (match uu____19505 with
                               | FStar_Pervasives_Native.Some
                                   {
                                     FStar_TypeChecker_Cfg.name = uu____19508;
                                     FStar_TypeChecker_Cfg.arity =
                                       uu____19509;
                                     FStar_TypeChecker_Cfg.auto_reflect =
                                       FStar_Pervasives_Native.Some n1;
                                     FStar_TypeChecker_Cfg.strong_reduction_ok
                                       = uu____19511;
                                     FStar_TypeChecker_Cfg.requires_binder_substitution
                                       = uu____19512;
                                     FStar_TypeChecker_Cfg.interpretation =
                                       uu____19513;_}
                                   when (FStar_List.length args) = n1 ->
                                   norm cfg env1 stack' t1
                               | uu____19528 -> fallback " (3)" ())
                          | uu____19531 -> fallback " (4)" ()))
                | uu____19532 -> fallback " (2)" ())
           | (App (env1,head1,aq,r))::stack1 ->
               let t2 =
                 FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild cfg env1 stack1 t2
           | (Match (env',branches,cfg1,r))::stack1 ->
               (FStar_TypeChecker_Cfg.log cfg1
                  (fun uu____19555  ->
                     let uu____19556 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1
                       "Rebuilding with match, scrutinee is %s ...\n"
                       uu____19556);
                (let scrutinee_env = env  in
                 let env1 = env'  in
                 let scrutinee = t1  in
                 let norm_and_rebuild_match uu____19565 =
                   FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____19570  ->
                        let uu____19571 =
                          FStar_Syntax_Print.term_to_string scrutinee  in
                        let uu____19572 =
                          let uu____19573 =
                            FStar_All.pipe_right branches
                              (FStar_List.map
                                 (fun uu____19600  ->
                                    match uu____19600 with
                                    | (p,uu____19610,uu____19611) ->
                                        FStar_Syntax_Print.pat_to_string p))
                             in
                          FStar_All.pipe_right uu____19573
                            (FStar_String.concat "\n\t")
                           in
                        FStar_Util.print2
                          "match is irreducible: scrutinee=%s\nbranches=%s\n"
                          uu____19571 uu____19572);
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
                             (fun uu___254_19628  ->
                                match uu___254_19628 with
                                | FStar_TypeChecker_Env.InliningDelta  ->
                                    true
                                | FStar_TypeChecker_Env.Eager_unfolding_only 
                                    -> true
                                | uu____19629 -> false))
                         in
                      let steps =
                        let uu___319_19631 = cfg1.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___319_19631.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___319_19631.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta = false;
                          FStar_TypeChecker_Cfg.weak =
                            (uu___319_19631.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___319_19631.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___319_19631.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___319_19631.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___319_19631.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_tac = false;
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___319_19631.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___319_19631.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___319_19631.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___319_19631.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___319_19631.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___319_19631.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___319_19631.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___319_19631.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___319_19631.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___319_19631.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___319_19631.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___319_19631.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___319_19631.FStar_TypeChecker_Cfg.nbe_step)
                        }  in
                      let uu___320_19636 = cfg1  in
                      {
                        FStar_TypeChecker_Cfg.steps = steps;
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___320_19636.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___320_19636.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level = new_delta;
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___320_19636.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong = true;
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___320_19636.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___320_19636.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying =
                          (uu___320_19636.FStar_TypeChecker_Cfg.reifying)
                      }  in
                    let norm_or_whnf env2 t2 =
                      if whnf
                      then closure_as_term cfg_exclude_zeta env2 t2
                      else norm cfg_exclude_zeta env2 [] t2  in
                    let rec norm_pat env2 p =
                      match p.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_constant uu____19708 ->
                          (p, env2)
                      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                          let uu____19737 =
                            FStar_All.pipe_right pats
                              (FStar_List.fold_left
                                 (fun uu____19821  ->
                                    fun uu____19822  ->
                                      match (uu____19821, uu____19822) with
                                      | ((pats1,env3),(p1,b)) ->
                                          let uu____19961 = norm_pat env3 p1
                                             in
                                          (match uu____19961 with
                                           | (p2,env4) ->
                                               (((p2, b) :: pats1), env4)))
                                 ([], env2))
                             in
                          (match uu____19737 with
                           | (pats1,env3) ->
                               ((let uu___321_20123 = p  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_cons
                                        (fv, (FStar_List.rev pats1)));
                                   FStar_Syntax_Syntax.p =
                                     (uu___321_20123.FStar_Syntax_Syntax.p)
                                 }), env3))
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let x1 =
                            let uu___322_20142 = x  in
                            let uu____20143 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___322_20142.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___322_20142.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20143
                            }  in
                          ((let uu___323_20157 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_var x1);
                              FStar_Syntax_Syntax.p =
                                (uu___323_20157.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let x1 =
                            let uu___324_20168 = x  in
                            let uu____20169 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___324_20168.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___324_20168.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20169
                            }  in
                          ((let uu___325_20183 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_wild x1);
                              FStar_Syntax_Syntax.p =
                                (uu___325_20183.FStar_Syntax_Syntax.p)
                            }), (dummy :: env2))
                      | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                          let x1 =
                            let uu___326_20199 = x  in
                            let uu____20200 =
                              norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                               in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___326_20199.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___326_20199.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____20200
                            }  in
                          let t3 = norm_or_whnf env2 t2  in
                          ((let uu___327_20215 = p  in
                            {
                              FStar_Syntax_Syntax.v =
                                (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                              FStar_Syntax_Syntax.p =
                                (uu___327_20215.FStar_Syntax_Syntax.p)
                            }), env2)
                       in
                    let branches1 =
                      match env1 with
                      | [] when whnf -> branches
                      | uu____20259 ->
                          FStar_All.pipe_right branches
                            (FStar_List.map
                               (fun branch1  ->
                                  let uu____20289 =
                                    FStar_Syntax_Subst.open_branch branch1
                                     in
                                  match uu____20289 with
                                  | (p,wopt,e) ->
                                      let uu____20309 = norm_pat env1 p  in
                                      (match uu____20309 with
                                       | (p1,env2) ->
                                           let wopt1 =
                                             match wopt with
                                             | FStar_Pervasives_Native.None 
                                                 ->
                                                 FStar_Pervasives_Native.None
                                             | FStar_Pervasives_Native.Some w
                                                 ->
                                                 let uu____20364 =
                                                   norm_or_whnf env2 w  in
                                                 FStar_Pervasives_Native.Some
                                                   uu____20364
                                              in
                                           let e1 = norm_or_whnf env2 e  in
                                           FStar_Syntax_Util.branch
                                             (p1, wopt1, e1))))
                       in
                    let scrutinee1 =
                      let uu____20381 =
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
                      if uu____20381
                      then
                        norm
                          (let uu___328_20386 = cfg1  in
                           {
                             FStar_TypeChecker_Cfg.steps =
                               (let uu___329_20389 =
                                  cfg1.FStar_TypeChecker_Cfg.steps  in
                                {
                                  FStar_TypeChecker_Cfg.beta =
                                    (uu___329_20389.FStar_TypeChecker_Cfg.beta);
                                  FStar_TypeChecker_Cfg.iota =
                                    (uu___329_20389.FStar_TypeChecker_Cfg.iota);
                                  FStar_TypeChecker_Cfg.zeta =
                                    (uu___329_20389.FStar_TypeChecker_Cfg.zeta);
                                  FStar_TypeChecker_Cfg.weak =
                                    (uu___329_20389.FStar_TypeChecker_Cfg.weak);
                                  FStar_TypeChecker_Cfg.hnf =
                                    (uu___329_20389.FStar_TypeChecker_Cfg.hnf);
                                  FStar_TypeChecker_Cfg.primops =
                                    (uu___329_20389.FStar_TypeChecker_Cfg.primops);
                                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                    =
                                    (uu___329_20389.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                  FStar_TypeChecker_Cfg.unfold_until =
                                    (uu___329_20389.FStar_TypeChecker_Cfg.unfold_until);
                                  FStar_TypeChecker_Cfg.unfold_only =
                                    (uu___329_20389.FStar_TypeChecker_Cfg.unfold_only);
                                  FStar_TypeChecker_Cfg.unfold_fully =
                                    (uu___329_20389.FStar_TypeChecker_Cfg.unfold_fully);
                                  FStar_TypeChecker_Cfg.unfold_attr =
                                    (uu___329_20389.FStar_TypeChecker_Cfg.unfold_attr);
                                  FStar_TypeChecker_Cfg.unfold_tac =
                                    (uu___329_20389.FStar_TypeChecker_Cfg.unfold_tac);
                                  FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                    =
                                    (uu___329_20389.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                  FStar_TypeChecker_Cfg.simplify =
                                    (uu___329_20389.FStar_TypeChecker_Cfg.simplify);
                                  FStar_TypeChecker_Cfg.erase_universes =
                                    (uu___329_20389.FStar_TypeChecker_Cfg.erase_universes);
                                  FStar_TypeChecker_Cfg.allow_unbound_universes
                                    =
                                    (uu___329_20389.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                  FStar_TypeChecker_Cfg.reify_ =
                                    (uu___329_20389.FStar_TypeChecker_Cfg.reify_);
                                  FStar_TypeChecker_Cfg.compress_uvars =
                                    (uu___329_20389.FStar_TypeChecker_Cfg.compress_uvars);
                                  FStar_TypeChecker_Cfg.no_full_norm =
                                    (uu___329_20389.FStar_TypeChecker_Cfg.no_full_norm);
                                  FStar_TypeChecker_Cfg.check_no_uvars =
                                    (uu___329_20389.FStar_TypeChecker_Cfg.check_no_uvars);
                                  FStar_TypeChecker_Cfg.unmeta =
                                    (uu___329_20389.FStar_TypeChecker_Cfg.unmeta);
                                  FStar_TypeChecker_Cfg.unascribe =
                                    (uu___329_20389.FStar_TypeChecker_Cfg.unascribe);
                                  FStar_TypeChecker_Cfg.in_full_norm_request
                                    =
                                    (uu___329_20389.FStar_TypeChecker_Cfg.in_full_norm_request);
                                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                    = false;
                                  FStar_TypeChecker_Cfg.nbe_step =
                                    (uu___329_20389.FStar_TypeChecker_Cfg.nbe_step)
                                });
                             FStar_TypeChecker_Cfg.tcenv =
                               (uu___328_20386.FStar_TypeChecker_Cfg.tcenv);
                             FStar_TypeChecker_Cfg.debug =
                               (uu___328_20386.FStar_TypeChecker_Cfg.debug);
                             FStar_TypeChecker_Cfg.delta_level =
                               (uu___328_20386.FStar_TypeChecker_Cfg.delta_level);
                             FStar_TypeChecker_Cfg.primitive_steps =
                               (uu___328_20386.FStar_TypeChecker_Cfg.primitive_steps);
                             FStar_TypeChecker_Cfg.strong =
                               (uu___328_20386.FStar_TypeChecker_Cfg.strong);
                             FStar_TypeChecker_Cfg.memoize_lazy =
                               (uu___328_20386.FStar_TypeChecker_Cfg.memoize_lazy);
                             FStar_TypeChecker_Cfg.normalize_pure_lets =
                               (uu___328_20386.FStar_TypeChecker_Cfg.normalize_pure_lets);
                             FStar_TypeChecker_Cfg.reifying =
                               (uu___328_20386.FStar_TypeChecker_Cfg.reifying)
                           }) scrutinee_env [] scrutinee
                      else scrutinee  in
                    let uu____20391 =
                      mk
                        (FStar_Syntax_Syntax.Tm_match (scrutinee1, branches1))
                        r
                       in
                    rebuild cfg1 env1 stack1 uu____20391)
                    in
                 let rec is_cons head1 =
                   let uu____20416 =
                     let uu____20417 = FStar_Syntax_Subst.compress head1  in
                     uu____20417.FStar_Syntax_Syntax.n  in
                   match uu____20416 with
                   | FStar_Syntax_Syntax.Tm_uinst (h,uu____20421) ->
                       is_cons h
                   | FStar_Syntax_Syntax.Tm_constant uu____20426 -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____20427;
                         FStar_Syntax_Syntax.fv_delta = uu____20428;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Data_ctor );_}
                       -> true
                   | FStar_Syntax_Syntax.Tm_fvar
                       { FStar_Syntax_Syntax.fv_name = uu____20429;
                         FStar_Syntax_Syntax.fv_delta = uu____20430;
                         FStar_Syntax_Syntax.fv_qual =
                           FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_ctor uu____20431);_}
                       -> true
                   | uu____20438 -> false  in
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
                   let uu____20601 =
                     FStar_Syntax_Util.head_and_args scrutinee1  in
                   match uu____20601 with
                   | (head1,args) ->
                       (match p.FStar_Syntax_Syntax.v with
                        | FStar_Syntax_Syntax.Pat_var bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_wild bv ->
                            FStar_Util.Inl [(bv, scrutinee_orig)]
                        | FStar_Syntax_Syntax.Pat_dot_term uu____20688 ->
                            FStar_Util.Inl []
                        | FStar_Syntax_Syntax.Pat_constant s ->
                            (match scrutinee1.FStar_Syntax_Syntax.n with
                             | FStar_Syntax_Syntax.Tm_constant s' when
                                 FStar_Const.eq_const s s' ->
                                 FStar_Util.Inl []
                             | uu____20727 ->
                                 let uu____20728 =
                                   let uu____20729 = is_cons head1  in
                                   Prims.op_Negation uu____20729  in
                                 FStar_Util.Inr uu____20728)
                        | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                            let uu____20754 =
                              let uu____20755 =
                                FStar_Syntax_Util.un_uinst head1  in
                              uu____20755.FStar_Syntax_Syntax.n  in
                            (match uu____20754 with
                             | FStar_Syntax_Syntax.Tm_fvar fv' when
                                 FStar_Syntax_Syntax.fv_eq fv fv' ->
                                 matches_args [] args arg_pats
                             | uu____20773 ->
                                 let uu____20774 =
                                   let uu____20775 = is_cons head1  in
                                   Prims.op_Negation uu____20775  in
                                 FStar_Util.Inr uu____20774))
                 
                 and matches_args out a p =
                   match (a, p) with
                   | ([],[]) -> FStar_Util.Inl out
                   | ((t2,uu____20852)::rest_a,(p1,uu____20855)::rest_p) ->
                       let uu____20899 = matches_pat t2 p1  in
                       (match uu____20899 with
                        | FStar_Util.Inl s ->
                            matches_args (FStar_List.append out s) rest_a
                              rest_p
                        | m -> m)
                   | uu____20948 -> FStar_Util.Inr false
                  in
                 let rec matches scrutinee1 p =
                   match p with
                   | [] -> norm_and_rebuild_match ()
                   | (p1,wopt,b)::rest ->
                       let uu____21066 = matches_pat scrutinee1 p1  in
                       (match uu____21066 with
                        | FStar_Util.Inr (false ) -> matches scrutinee1 rest
                        | FStar_Util.Inr (true ) -> norm_and_rebuild_match ()
                        | FStar_Util.Inl s ->
                            (FStar_TypeChecker_Cfg.log cfg1
                               (fun uu____21106  ->
                                  let uu____21107 =
                                    FStar_Syntax_Print.pat_to_string p1  in
                                  let uu____21108 =
                                    let uu____21109 =
                                      FStar_List.map
                                        (fun uu____21119  ->
                                           match uu____21119 with
                                           | (uu____21124,t2) ->
                                               FStar_Syntax_Print.term_to_string
                                                 t2) s
                                       in
                                    FStar_All.pipe_right uu____21109
                                      (FStar_String.concat "; ")
                                     in
                                  FStar_Util.print2
                                    "Matches pattern %s with subst = %s\n"
                                    uu____21107 uu____21108);
                             (let env0 = env1  in
                              let env2 =
                                FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____21156  ->
                                       match uu____21156 with
                                       | (bv,t2) ->
                                           let uu____21179 =
                                             let uu____21186 =
                                               let uu____21189 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   bv
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____21189
                                                in
                                             let uu____21190 =
                                               let uu____21191 =
                                                 let uu____21222 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], t2))
                                                    in
                                                 ([], t2, uu____21222, false)
                                                  in
                                               Clos uu____21191  in
                                             (uu____21186, uu____21190)  in
                                           uu____21179 :: env2) env1 s
                                 in
                              let uu____21335 = guard_when_clause wopt b rest
                                 in
                              norm cfg1 env2 stack1 uu____21335)))
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
          let c = FStar_TypeChecker_Cfg.config' ps s e  in norm c [] [] t
  
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
        let uu____21398 = FStar_TypeChecker_Cfg.config s e  in
        norm_comp uu____21398 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____21415 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____21415 [] u
  
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
        let uu____21439 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____21439  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____21446 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___330_21465 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___330_21465.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___330_21465.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name
              cfg.FStar_TypeChecker_Cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____21472 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____21472
          then
            let ct1 =
              let uu____21474 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____21474 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags1 =
                    let uu____21481 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____21481
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___331_21485 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___331_21485.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___331_21485.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___331_21485.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags1
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev
                      cfg.FStar_TypeChecker_Cfg.tcenv c
                     in
                  let uu___332_21487 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___332_21487.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___332_21487.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___332_21487.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___332_21487.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___333_21488 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___333_21488.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___333_21488.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____21490 -> c
  
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
        let uu____21508 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____21508  in
      let uu____21515 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____21515
      then
        let uu____21516 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____21516 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____21522  ->
                 let uu____21523 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____21523)
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
            ((let uu____21544 =
                let uu____21549 =
                  let uu____21550 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____21550
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____21549)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____21544);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          let uu____21565 =
            FStar_TypeChecker_Cfg.config
              [FStar_TypeChecker_Env.AllowUnboundUniverses] env
             in
          norm_comp uu____21565 [] c
        with
        | e ->
            ((let uu____21578 =
                let uu____21583 =
                  let uu____21584 = FStar_Util.message_of_exn e  in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____21584
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____21583)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____21578);
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
                   let uu____21629 =
                     let uu____21630 =
                       let uu____21637 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____21637)  in
                     FStar_Syntax_Syntax.Tm_refine uu____21630  in
                   mk uu____21629 t01.FStar_Syntax_Syntax.pos
               | uu____21642 -> t2)
          | uu____21643 -> t2  in
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
        let uu____21707 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____21707 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____21736 ->
                 let uu____21743 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____21743 with
                  | (actuals,uu____21753,uu____21754) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____21768 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____21768 with
                         | (binders,args) ->
                             let uu____21779 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____21779
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
      | uu____21793 ->
          let uu____21794 = FStar_Syntax_Util.head_and_args t  in
          (match uu____21794 with
           | (head1,args) ->
               let uu____21831 =
                 let uu____21832 = FStar_Syntax_Subst.compress head1  in
                 uu____21832.FStar_Syntax_Syntax.n  in
               (match uu____21831 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____21853 =
                      let uu____21866 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____21866  in
                    (match uu____21853 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____21896 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___338_21904 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___338_21904.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___338_21904.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___338_21904.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___338_21904.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___338_21904.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___338_21904.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___338_21904.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___338_21904.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___338_21904.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___338_21904.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___338_21904.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___338_21904.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___338_21904.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___338_21904.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___338_21904.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___338_21904.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___338_21904.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___338_21904.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___338_21904.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___338_21904.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___338_21904.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___338_21904.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___338_21904.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___338_21904.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___338_21904.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___338_21904.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___338_21904.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___338_21904.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___338_21904.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___338_21904.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___338_21904.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___338_21904.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___338_21904.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___338_21904.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___338_21904.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.dep_graph =
                                     (uu___338_21904.FStar_TypeChecker_Env.dep_graph);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___338_21904.FStar_TypeChecker_Env.nbe)
                                 }) t
                               in
                            match uu____21896 with
                            | (uu____21905,ty,uu____21907) ->
                                eta_expand_with_type env t ty))
                | uu____21908 ->
                    let uu____21909 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___339_21917 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___339_21917.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___339_21917.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___339_21917.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___339_21917.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___339_21917.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___339_21917.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___339_21917.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___339_21917.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___339_21917.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___339_21917.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___339_21917.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___339_21917.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___339_21917.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___339_21917.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___339_21917.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___339_21917.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___339_21917.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___339_21917.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___339_21917.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.failhard =
                             (uu___339_21917.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___339_21917.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___339_21917.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___339_21917.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___339_21917.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___339_21917.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___339_21917.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___339_21917.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___339_21917.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___339_21917.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___339_21917.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___339_21917.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___339_21917.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___339_21917.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___339_21917.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___339_21917.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.dep_graph =
                             (uu___339_21917.FStar_TypeChecker_Env.dep_graph);
                           FStar_TypeChecker_Env.nbe =
                             (uu___339_21917.FStar_TypeChecker_Env.nbe)
                         }) t
                       in
                    (match uu____21909 with
                     | (uu____21918,ty,uu____21920) ->
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
      let uu___340_21993 = x  in
      let uu____21994 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___340_21993.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___340_21993.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____21994
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____21997 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____22020 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____22021 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____22022 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____22023 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____22030 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____22031 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____22032 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___341_22062 = rc  in
          let uu____22063 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____22072 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___341_22062.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____22063;
            FStar_Syntax_Syntax.residual_flags = uu____22072
          }  in
        let uu____22075 =
          let uu____22076 =
            let uu____22093 = elim_delayed_subst_binders bs  in
            let uu____22100 = elim_delayed_subst_term t2  in
            let uu____22103 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____22093, uu____22100, uu____22103)  in
          FStar_Syntax_Syntax.Tm_abs uu____22076  in
        mk1 uu____22075
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____22134 =
          let uu____22135 =
            let uu____22148 = elim_delayed_subst_binders bs  in
            let uu____22155 = elim_delayed_subst_comp c  in
            (uu____22148, uu____22155)  in
          FStar_Syntax_Syntax.Tm_arrow uu____22135  in
        mk1 uu____22134
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____22172 =
          let uu____22173 =
            let uu____22180 = elim_bv bv  in
            let uu____22181 = elim_delayed_subst_term phi  in
            (uu____22180, uu____22181)  in
          FStar_Syntax_Syntax.Tm_refine uu____22173  in
        mk1 uu____22172
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____22208 =
          let uu____22209 =
            let uu____22224 = elim_delayed_subst_term t2  in
            let uu____22227 = elim_delayed_subst_args args  in
            (uu____22224, uu____22227)  in
          FStar_Syntax_Syntax.Tm_app uu____22209  in
        mk1 uu____22208
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___342_22295 = p  in
              let uu____22296 =
                let uu____22297 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____22297  in
              {
                FStar_Syntax_Syntax.v = uu____22296;
                FStar_Syntax_Syntax.p =
                  (uu___342_22295.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___343_22299 = p  in
              let uu____22300 =
                let uu____22301 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____22301  in
              {
                FStar_Syntax_Syntax.v = uu____22300;
                FStar_Syntax_Syntax.p =
                  (uu___343_22299.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___344_22308 = p  in
              let uu____22309 =
                let uu____22310 =
                  let uu____22317 = elim_bv x  in
                  let uu____22318 = elim_delayed_subst_term t0  in
                  (uu____22317, uu____22318)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____22310  in
              {
                FStar_Syntax_Syntax.v = uu____22309;
                FStar_Syntax_Syntax.p =
                  (uu___344_22308.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___345_22341 = p  in
              let uu____22342 =
                let uu____22343 =
                  let uu____22356 =
                    FStar_List.map
                      (fun uu____22379  ->
                         match uu____22379 with
                         | (x,b) ->
                             let uu____22392 = elim_pat x  in
                             (uu____22392, b)) pats
                     in
                  (fv, uu____22356)  in
                FStar_Syntax_Syntax.Pat_cons uu____22343  in
              {
                FStar_Syntax_Syntax.v = uu____22342;
                FStar_Syntax_Syntax.p =
                  (uu___345_22341.FStar_Syntax_Syntax.p)
              }
          | uu____22405 -> p  in
        let elim_branch uu____22429 =
          match uu____22429 with
          | (pat,wopt,t3) ->
              let uu____22455 = elim_pat pat  in
              let uu____22458 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____22461 = elim_delayed_subst_term t3  in
              (uu____22455, uu____22458, uu____22461)
           in
        let uu____22466 =
          let uu____22467 =
            let uu____22490 = elim_delayed_subst_term t2  in
            let uu____22493 = FStar_List.map elim_branch branches  in
            (uu____22490, uu____22493)  in
          FStar_Syntax_Syntax.Tm_match uu____22467  in
        mk1 uu____22466
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____22624 =
          match uu____22624 with
          | (tc,topt) ->
              let uu____22659 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____22669 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____22669
                | FStar_Util.Inr c ->
                    let uu____22671 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____22671
                 in
              let uu____22672 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____22659, uu____22672)
           in
        let uu____22681 =
          let uu____22682 =
            let uu____22709 = elim_delayed_subst_term t2  in
            let uu____22712 = elim_ascription a  in
            (uu____22709, uu____22712, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____22682  in
        mk1 uu____22681
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___346_22773 = lb  in
          let uu____22774 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____22777 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___346_22773.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___346_22773.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____22774;
            FStar_Syntax_Syntax.lbeff =
              (uu___346_22773.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____22777;
            FStar_Syntax_Syntax.lbattrs =
              (uu___346_22773.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___346_22773.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____22780 =
          let uu____22781 =
            let uu____22794 =
              let uu____22801 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____22801)  in
            let uu____22810 = elim_delayed_subst_term t2  in
            (uu____22794, uu____22810)  in
          FStar_Syntax_Syntax.Tm_let uu____22781  in
        mk1 uu____22780
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____22854 =
          let uu____22855 =
            let uu____22862 = elim_delayed_subst_term tm  in
            (uu____22862, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____22855  in
        mk1 uu____22854
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____22873 =
          let uu____22874 =
            let uu____22881 = elim_delayed_subst_term t2  in
            let uu____22884 = elim_delayed_subst_meta md  in
            (uu____22881, uu____22884)  in
          FStar_Syntax_Syntax.Tm_meta uu____22874  in
        mk1 uu____22873

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    FStar_List.map
      (fun uu___255_22893  ->
         match uu___255_22893 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____22897 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____22897
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
        let uu____22920 =
          let uu____22921 =
            let uu____22930 = elim_delayed_subst_term t  in
            (uu____22930, uopt)  in
          FStar_Syntax_Syntax.Total uu____22921  in
        mk1 uu____22920
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____22947 =
          let uu____22948 =
            let uu____22957 = elim_delayed_subst_term t  in
            (uu____22957, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____22948  in
        mk1 uu____22947
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___347_22966 = ct  in
          let uu____22967 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____22970 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____22979 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___347_22966.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___347_22966.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____22967;
            FStar_Syntax_Syntax.effect_args = uu____22970;
            FStar_Syntax_Syntax.flags = uu____22979
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___256_22982  ->
    match uu___256_22982 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____22994 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____22994
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____23027 =
          let uu____23034 = elim_delayed_subst_term t  in (m, uu____23034)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____23027
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____23046 =
          let uu____23055 = elim_delayed_subst_term t  in
          (m1, m2, uu____23055)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____23046
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____23082  ->
         match uu____23082 with
         | (t,q) ->
             let uu____23093 = elim_delayed_subst_term t  in (uu____23093, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____23113  ->
         match uu____23113 with
         | (x,q) ->
             let uu____23124 =
               let uu___348_23125 = x  in
               let uu____23126 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___348_23125.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___348_23125.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____23126
               }  in
             (uu____23124, q)) bs

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
            | (uu____23218,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____23244,FStar_Util.Inl t) ->
                let uu____23262 =
                  let uu____23269 =
                    let uu____23270 =
                      let uu____23283 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____23283)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____23270  in
                  FStar_Syntax_Syntax.mk uu____23269  in
                uu____23262 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____23297 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____23297 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____23327 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____23390 ->
                    let uu____23391 =
                      let uu____23400 =
                        let uu____23401 = FStar_Syntax_Subst.compress t4  in
                        uu____23401.FStar_Syntax_Syntax.n  in
                      (uu____23400, tc)  in
                    (match uu____23391 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____23428) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____23469) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____23508,FStar_Util.Inl uu____23509) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____23536 -> failwith "Impossible")
                 in
              (match uu____23327 with
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
          let uu____23661 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____23661 with
          | (univ_names1,binders1,tc) ->
              let uu____23727 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____23727)
  
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
          let uu____23776 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____23776 with
          | (univ_names1,binders1,tc) ->
              let uu____23842 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____23842)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____23881 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____23881 with
           | (univ_names1,binders1,typ1) ->
               let uu___349_23915 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___349_23915.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___349_23915.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___349_23915.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___349_23915.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___350_23930 = s  in
          let uu____23931 =
            let uu____23932 =
              let uu____23941 = FStar_List.map (elim_uvars env) sigs  in
              (uu____23941, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____23932  in
          {
            FStar_Syntax_Syntax.sigel = uu____23931;
            FStar_Syntax_Syntax.sigrng =
              (uu___350_23930.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___350_23930.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___350_23930.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___350_23930.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____23958 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____23958 with
           | (univ_names1,uu____23978,typ1) ->
               let uu___351_23996 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___351_23996.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___351_23996.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___351_23996.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___351_23996.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____24002 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____24002 with
           | (univ_names1,uu____24022,typ1) ->
               let uu___352_24040 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___352_24040.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___352_24040.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___352_24040.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___352_24040.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____24068 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____24068 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____24093 =
                            let uu____24094 =
                              let uu____24095 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____24095  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____24094
                             in
                          elim_delayed_subst_term uu____24093  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___353_24098 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___353_24098.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___353_24098.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___353_24098.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___353_24098.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___354_24099 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___354_24099.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___354_24099.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___354_24099.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___354_24099.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___355_24105 = s  in
          let uu____24106 =
            let uu____24107 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____24107  in
          {
            FStar_Syntax_Syntax.sigel = uu____24106;
            FStar_Syntax_Syntax.sigrng =
              (uu___355_24105.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___355_24105.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___355_24105.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___355_24105.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____24111 = elim_uvars_aux_t env us [] t  in
          (match uu____24111 with
           | (us1,uu____24131,t1) ->
               let uu___356_24149 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___356_24149.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___356_24149.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___356_24149.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___356_24149.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____24150 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____24152 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____24152 with
           | (univs1,binders,signature) ->
               let uu____24186 =
                 let uu____24191 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____24191 with
                 | (univs_opening,univs2) ->
                     let uu____24214 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____24214)
                  in
               (match uu____24186 with
                | (univs_opening,univs_closing) ->
                    let uu____24217 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____24223 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____24224 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____24223, uu____24224)  in
                    (match uu____24217 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____24248 =
                           match uu____24248 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____24266 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____24266 with
                                | (us1,t1) ->
                                    let uu____24277 =
                                      let uu____24286 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____24297 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____24286, uu____24297)  in
                                    (match uu____24277 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____24326 =
                                           let uu____24335 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____24346 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____24335, uu____24346)  in
                                         (match uu____24326 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____24376 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____24376
                                                 in
                                              let uu____24377 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____24377 with
                                               | (uu____24400,uu____24401,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____24420 =
                                                       let uu____24421 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____24421
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____24420
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____24430 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____24430 with
                           | (uu____24447,uu____24448,t1) -> t1  in
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
                             | uu____24518 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____24543 =
                               let uu____24544 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____24544.FStar_Syntax_Syntax.n  in
                             match uu____24543 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____24603 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____24634 =
                               let uu____24635 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____24635.FStar_Syntax_Syntax.n  in
                             match uu____24634 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____24656) ->
                                 let uu____24677 = destruct_action_body body
                                    in
                                 (match uu____24677 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____24722 ->
                                 let uu____24723 = destruct_action_body t  in
                                 (match uu____24723 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____24772 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____24772 with
                           | (action_univs,t) ->
                               let uu____24781 = destruct_action_typ_templ t
                                  in
                               (match uu____24781 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___357_24822 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___357_24822.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___357_24822.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___358_24824 = ed  in
                           let uu____24825 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____24826 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____24827 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____24828 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____24829 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____24830 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____24831 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____24832 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____24833 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____24834 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____24835 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____24836 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____24837 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____24838 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___358_24824.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___358_24824.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____24825;
                             FStar_Syntax_Syntax.bind_wp = uu____24826;
                             FStar_Syntax_Syntax.if_then_else = uu____24827;
                             FStar_Syntax_Syntax.ite_wp = uu____24828;
                             FStar_Syntax_Syntax.stronger = uu____24829;
                             FStar_Syntax_Syntax.close_wp = uu____24830;
                             FStar_Syntax_Syntax.assert_p = uu____24831;
                             FStar_Syntax_Syntax.assume_p = uu____24832;
                             FStar_Syntax_Syntax.null_wp = uu____24833;
                             FStar_Syntax_Syntax.trivial = uu____24834;
                             FStar_Syntax_Syntax.repr = uu____24835;
                             FStar_Syntax_Syntax.return_repr = uu____24836;
                             FStar_Syntax_Syntax.bind_repr = uu____24837;
                             FStar_Syntax_Syntax.actions = uu____24838;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___358_24824.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___359_24841 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___359_24841.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___359_24841.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___359_24841.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___359_24841.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___257_24862 =
            match uu___257_24862 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____24893 = elim_uvars_aux_t env us [] t  in
                (match uu____24893 with
                 | (us1,uu____24921,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___360_24948 = sub_eff  in
            let uu____24949 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____24952 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___360_24948.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___360_24948.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____24949;
              FStar_Syntax_Syntax.lift = uu____24952
            }  in
          let uu___361_24955 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___361_24955.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___361_24955.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___361_24955.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___361_24955.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags1) ->
          let uu____24965 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____24965 with
           | (univ_names1,binders1,comp1) ->
               let uu___362_24999 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___362_24999.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___362_24999.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___362_24999.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___362_24999.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____25002 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____25003 -> s
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      normalize
        [FStar_TypeChecker_Env.EraseUniverses;
        FStar_TypeChecker_Env.AllowUnboundUniverses] env t
  