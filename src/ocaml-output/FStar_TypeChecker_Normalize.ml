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
    match projectee with | Clos _0 -> true | uu____145 -> false
  
let (__proj__Clos__item___0 :
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
      Prims.list * FStar_Syntax_Syntax.term * ((FStar_Syntax_Syntax.binder
      FStar_Pervasives_Native.option * closure) Prims.list *
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool))
  = fun projectee  -> match projectee with | Clos _0 -> _0 
let (uu___is_Univ : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____281 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____299 -> false
  
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
    match projectee with | Arg _0 -> true | uu____572 -> false
  
let (__proj__Arg__item___0 :
  stack_elt -> (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)) =
  fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____615 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range))
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____662 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo) =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____754 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env * branches * FStar_TypeChecker_Cfg.cfg * FStar_Range.range))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____921 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * env *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
      FStar_Range.range))
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____1009 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Range.range))
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1070 -> false
  
let (__proj__Meta__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.metadata * FStar_Range.range)) =
  fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____1122 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding *
      FStar_Range.range))
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____1221 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> FStar_TypeChecker_Cfg.cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____1423 -> false
  
let (__proj__Debug__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.term * FStar_Util.time)) =
  fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____1476 = FStar_Syntax_Util.head_and_args' t  in
    match uu____1476 with | (hd1,uu____1504) -> hd1
  
let mk :
  'Auu____1548 .
    'Auu____1548 ->
      FStar_Range.range -> 'Auu____1548 FStar_Syntax_Syntax.syntax
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
          let uu____1665 = FStar_ST.op_Bang r  in
          match uu____1665 with
          | FStar_Pervasives_Native.Some uu____1691 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____1746 =
      FStar_List.map
        (fun uu____1762  ->
           match uu____1762 with
           | (bopt,c) ->
               let uu____1776 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____1781 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____1776 uu____1781) env
       in
    FStar_All.pipe_right uu____1746 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___1_1789  ->
    match uu___1_1789 with
    | Clos (env,t,uu____1793,uu____1794) ->
        let uu____1857 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____1867 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____1857 uu____1867
    | Univ uu____1870 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___2_1879  ->
    match uu___2_1879 with
    | Arg (c,uu____1882,uu____1883) ->
        let uu____1884 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____1884
    | MemoLazy uu____1887 -> "MemoLazy"
    | Abs (uu____1899,bs,uu____1901,uu____1902,uu____1903) ->
        let uu____1922 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____1922
    | UnivArgs uu____1938 -> "UnivArgs"
    | Match uu____1946 -> "Match"
    | App (uu____1991,t,uu____1993,uu____1994) ->
        let uu____2003 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____2003
    | Meta (uu____2006,m,uu____2008) -> "Meta"
    | Let uu____2010 -> "Let"
    | Cfg uu____2027 -> "Cfg"
    | Debug (t,uu____2065) ->
        let uu____2074 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____2074
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____2088 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____2088 (FStar_String.concat "; ")
  
let is_empty : 'Auu____2103 . 'Auu____2103 Prims.list -> Prims.bool =
  fun uu___3_2111  ->
    match uu___3_2111 with | [] -> true | uu____2115 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        (fun uu___115_2158  ->
           match () with
           | () ->
               let uu____2159 =
                 FStar_List.nth env x.FStar_Syntax_Syntax.index  in
               FStar_Pervasives_Native.snd uu____2159) ()
      with
      | uu___114_2176 ->
          let uu____2177 =
            let uu____2179 = FStar_Syntax_Print.db_to_string x  in
            let uu____2181 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____2179
              uu____2181
             in
          failwith uu____2177
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____2204 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____2204
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____2219 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____2219
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____2234 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____2234
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
          let uu____2354 =
            FStar_List.fold_left
              (fun uu____2380  ->
                 fun u1  ->
                   match uu____2380 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____2405 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____2405 with
                        | (k_u,n1) ->
                            let uu____2423 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____2423
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____2354 with
          | (uu____2444,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 (fun uu___149_2470  ->
                    match () with
                    | () ->
                        let uu____2473 =
                          let uu____2474 = FStar_List.nth env x  in
                          FStar_Pervasives_Native.snd uu____2474  in
                        (match uu____2473 with
                         | Univ u3 ->
                             ((let uu____2493 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      cfg.FStar_TypeChecker_Cfg.tcenv)
                                   (FStar_Options.Other "univ_norm")
                                  in
                               if uu____2493
                               then
                                 let uu____2498 =
                                   FStar_Syntax_Print.univ_to_string u3  in
                                 FStar_Util.print1
                                   "Univ (in norm_universe): %s\n" uu____2498
                               else ());
                              aux u3)
                         | Dummy  -> [u2]
                         | uu____2503 ->
                             let uu____2504 =
                               let uu____2506 = FStar_Util.string_of_int x
                                  in
                               FStar_Util.format1
                                 "Impossible: universe variable u@%s bound to a term"
                                 uu____2506
                                in
                             failwith uu____2504)) ()
               with
               | uu____2516 ->
                   if
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else
                     (let uu____2522 =
                        let uu____2524 = FStar_Util.string_of_int x  in
                        FStar_String.op_Hat "Universe variable not found: u@"
                          uu____2524
                         in
                      failwith uu____2522))
          | FStar_Syntax_Syntax.U_unif uu____2529 when
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____2540 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____2551 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____2560 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____2560 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____2577 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____2577 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____2588 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____2598 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____2598 with
                                  | (uu____2605,m) -> n1 <= m))
                           in
                        if uu____2588 then rest1 else us1
                    | uu____2614 -> us1)
               | uu____2620 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____2624 = aux u3  in
              FStar_List.map (fun _2627  -> FStar_Syntax_Syntax.U_succ _2627)
                uu____2624
           in
        if
          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____2631 = aux u  in
           match uu____2631 with
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
            (fun uu____3140  ->
               let uu____3141 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3143 = env_to_string env  in
               let uu____3145 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____3141 uu____3143 uu____3145);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____3162 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____3169 ->
                    let uu____3200 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____3200
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____3209 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____3210 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____3216 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____3221 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____3281 ->
                           let uu____3302 =
                             let uu____3304 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____3306 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____3304 uu____3306
                              in
                           failwith uu____3302
                       | uu____3315 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___4_3351  ->
                                         match uu___4_3351 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____3376 =
                                               let uu____3392 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____3392)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____3376
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___243_3439 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___243_3439.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___243_3439.FStar_Syntax_Syntax.sort)
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
                                              | uu____3473 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____3485 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___252_3498 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___252_3498.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___252_3498.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____3543 =
                        let uu____3544 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____3544  in
                      mk uu____3543 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____3568 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____3568  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____3575 = lookup_bvar env x  in
                    (match uu____3575 with
                     | Univ uu____3582 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___268_3601 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___268_3601.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___268_3601.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____3625,uu____3626) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____3753  ->
                              fun stack1  ->
                                match uu____3753 with
                                | (a,aq) ->
                                    let uu____3777 =
                                      let uu____3778 =
                                        let uu____3785 =
                                          let uu____3786 =
                                            let uu____3826 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____3826, false)  in
                                          Clos uu____3786  in
                                        (uu____3785, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____3778  in
                                    uu____3777 :: stack1) args)
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
                    let uu____4081 = close_binders cfg env bs  in
                    (match uu____4081 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,uu____4175) when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    ->
                    inline_closure_env cfg env stack
                      x.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____4222 =
                      let uu____4240 =
                        let uu____4254 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____4254]  in
                      close_binders cfg env uu____4240  in
                    (match uu____4222 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____4344 =
                             let uu____4345 =
                               let uu____4361 =
                                 let uu____4372 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____4372
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____4361, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____4345  in
                           mk uu____4344 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____4585 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____4585
                      | FStar_Util.Inr c ->
                          let uu____4627 = close_comp cfg env c  in
                          FStar_Util.Inr uu____4627
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____4682 =
                        let uu____4683 =
                          let uu____4730 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____4730, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____4683  in
                      mk uu____4682 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____4840 =
                            let uu____4841 =
                              let uu____4854 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____4854, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____4841  in
                          mk uu____4840 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____4986  -> dummy :: env1) env
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
                    let uu____5025 =
                      let uu____5048 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____5048
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____5126 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___360_5170 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___360_5170.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___360_5170.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____5126))
                       in
                    (match uu____5025 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___365_5240 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___365_5240.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___365_5240.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___365_5240.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___365_5240.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____5311,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____5429  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____5448 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____5448
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____5470  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____5517 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____5517
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___388_5562 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___388_5562.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___388_5562.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___391_5573 = lb  in
                      let uu____5588 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___391_5573.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___391_5573.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____5588;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___391_5573.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___391_5573.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____5678  -> fun env1  -> dummy :: env1)
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
            (fun uu____5946  ->
               let uu____5947 = FStar_Syntax_Print.tag_of_term t  in
               let uu____5949 = env_to_string env  in
               let uu____5951 = stack_to_string stack  in
               let uu____5953 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____5947 uu____5949 uu____5951 uu____5953);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____5964,uu____5965),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____6100 = close_binders cfg env' bs  in
               (match uu____6100 with
                | (bs1,uu____6125) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____6162 =
                      let uu___449_6173 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___449_6173.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___449_6173.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____6162)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____6329 =
                 match uu____6329 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____6494 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____6540 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____6644  ->
                                     fun uu____6645  ->
                                       match (uu____6644, uu____6645) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____6822 = norm_pat env4 p1
                                              in
                                           (match uu____6822 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____6540 with
                            | (pats1,env4) ->
                                ((let uu___486_7031 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___486_7031.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___490_7079 = x  in
                             let uu____7090 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___490_7079.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___490_7079.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____7090
                             }  in
                           ((let uu___493_7115 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___493_7115.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___497_7144 = x  in
                             let uu____7155 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___497_7144.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___497_7144.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____7155
                             }  in
                           ((let uu___500_7180 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___500_7180.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___506_7227 = x  in
                             let uu____7238 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___506_7227.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___506_7227.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____7238
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___510_7274 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___510_7274.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____7291 = norm_pat env2 pat  in
                     (match uu____7291 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____7404 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____7404
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____7462 =
                   let uu____7463 =
                     let uu____7501 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____7501)  in
                   FStar_Syntax_Syntax.Tm_match uu____7463  in
                 mk uu____7462 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern (names1,args) ->
                     let uu____7723 =
                       let uu____7752 =
                         FStar_All.pipe_right names1
                           (FStar_List.map
                              (non_tail_inline_closure_env cfg env_m))
                          in
                       let uu____7789 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun args1  ->
                                 FStar_All.pipe_right args1
                                   (FStar_List.map
                                      (fun uu____7938  ->
                                         match uu____7938 with
                                         | (a,q) ->
                                             let uu____7981 =
                                               non_tail_inline_closure_env
                                                 cfg env_m a
                                                in
                                             (uu____7981, q)))))
                          in
                       (uu____7752, uu____7789)  in
                     FStar_Syntax_Syntax.Meta_pattern uu____7723
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____8046 =
                       let uu____8061 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____8061)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____8046
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____8113 =
                       let uu____8134 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____8134)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____8113
                 | uu____8159 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____8177 -> failwith "Impossible: unexpected stack element")

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
            let uu____8236 =
              let uu____8237 = inline_closure_env cfg env [] t  in
              FStar_Syntax_Syntax.Meta uu____8237  in
            FStar_Pervasives_Native.Some uu____8236
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
        let uu____8302 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____8411  ->
                  fun uu____8412  ->
                    match (uu____8411, uu____8412) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___565_8617 = b  in
                          let uu____8628 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___565_8617.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___565_8617.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____8628
                          }  in
                        let imp1 = close_imp cfg env1 imp  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp1) :: out))) (env, []))
           in
        match uu____8302 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____8871 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____8896 = inline_closure_env cfg env [] t  in
                 let uu____8905 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____8896 uu____8905
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____8926 = inline_closure_env cfg env [] t  in
                 let uu____8935 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____8926 uu____8935
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____9022  ->
                           match uu____9022 with
                           | (a,q) ->
                               let uu____9059 =
                                 inline_closure_env cfg env [] a  in
                               (uu____9059, q)))
                    in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___5_9088  ->
                           match uu___5_9088 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____9096 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____9096
                           | f -> f))
                    in
                 let uu____9108 =
                   let uu___598_9119 = c1  in
                   let uu____9130 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____9130;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___598_9119.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____9108)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___6_9140  ->
            match uu___6_9140 with
            | FStar_Syntax_Syntax.DECREASES uu____9142 -> false
            | uu____9150 -> true))

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
                   (fun uu___7_9232  ->
                      match uu___7_9232 with
                      | FStar_Syntax_Syntax.DECREASES uu____9234 -> false
                      | uu____9242 -> true))
               in
            let rc1 =
              let uu___615_9259 = rc  in
              let uu____9274 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___615_9259.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____9274;
                FStar_Syntax_Syntax.residual_flags = flags
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____9302 -> lopt

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
    let uu____9447 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____9447 with
    | FStar_Pervasives_Native.Some e ->
        let uu____9486 = FStar_Syntax_Embeddings.unembed e t  in
        uu____9486 true FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____9506 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv * 'Auu____9506) FStar_Pervasives_Native.option
        * closure) Prims.list -> FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____9653  ->
           fun subst1  ->
             match uu____9653 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____9714,uu____9715)) ->
                      let uu____9807 = b  in
                      (match uu____9807 with
                       | (bv,uu____9820) ->
                           let uu____9831 =
                             let uu____9833 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____9833  in
                           if uu____9831
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____9849 = unembed_binder term1  in
                              match uu____9849 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____9866 =
                                      let uu___650_9877 = bv  in
                                      let uu____9888 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___650_9877.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___650_9877.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____9888
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____9866
                                     in
                                  let b_for_x =
                                    let uu____9907 =
                                      let uu____9923 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____9923)
                                       in
                                    FStar_Syntax_Syntax.NT uu____9907  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___8_9961  ->
                                         match uu___8_9961 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____9963,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____9965;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____9966;_})
                                             ->
                                             let uu____9994 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____9994
                                         | uu____9996 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____9998 -> subst1)) env []
  
let reduce_primops :
  'Auu____10025 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'Auu____10025)
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
            (let uu____10169 = FStar_Syntax_Util.head_and_args tm  in
             match uu____10169 with
             | (head1,args) ->
                 let uu____10242 =
                   let uu____10243 = FStar_Syntax_Util.un_uinst head1  in
                   uu____10243.FStar_Syntax_Syntax.n  in
                 (match uu____10242 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____10264 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                      (match uu____10264 with
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
                                (fun uu____10335  ->
                                   let uu____10336 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name
                                      in
                                   let uu____10338 =
                                     FStar_Util.string_of_int l  in
                                   let uu____10340 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____10336 uu____10338 uu____10340);
                              tm)
                           else
                             (let uu____10345 =
                                if l = prim_step.FStar_TypeChecker_Cfg.arity
                                then (args, [])
                                else
                                  FStar_List.splitAt
                                    prim_step.FStar_TypeChecker_Cfg.arity
                                    args
                                 in
                              match uu____10345 with
                              | (args_1,args_2) ->
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____10463  ->
                                        let uu____10464 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____10464);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____10473  ->
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
                                           (fun uu____10503  ->
                                              let uu____10504 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____10504);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____10520  ->
                                              let uu____10521 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____10523 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____10521 uu____10523);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____10526 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____10554  ->
                                 let uu____10555 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____10555);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____10573  ->
                            let uu____10574 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10574);
                       (match args with
                        | (a1,uu____10584)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____10625 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____10643  ->
                            let uu____10644 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____10644);
                       (match args with
                        | (t,uu____10654)::(r,uu____10656)::[] ->
                            let uu____10725 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____10725 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____10735 -> tm))
                  | uu____10750 -> tm))
  
let reduce_equality :
  'Auu____10761 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'Auu____10761)
          FStar_Pervasives_Native.option * closure) Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun tm  ->
        reduce_primops norm_cb
          (let uu___738_10898 = cfg  in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___740_10971 = FStar_TypeChecker_Cfg.default_steps  in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___740_10971.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___740_10971.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___740_10971.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___740_10971.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___740_10971.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___740_10971.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___740_10971.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___740_10971.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___740_10971.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___740_10971.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___740_10971.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___740_10971.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___740_10971.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___740_10971.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___740_10971.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___740_10971.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___740_10971.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___740_10971.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___740_10971.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___740_10971.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___740_10971.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___740_10971.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___740_10971.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___740_10971.FStar_TypeChecker_Cfg.nbe_step);
                  FStar_TypeChecker_Cfg.for_extraction =
                    (uu___740_10971.FStar_TypeChecker_Cfg.for_extraction)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___738_10898.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___738_10898.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___738_10898.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___738_10898.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___738_10898.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___738_10898.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___738_10898.FStar_TypeChecker_Cfg.reifying)
           }) tm
  
type norm_request_t =
  | Norm_request_none 
  | Norm_request_ready 
  | Norm_request_requires_rejig 
let (uu___is_Norm_request_none : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_none  -> true | uu____11034 -> false
  
let (uu___is_Norm_request_ready : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_ready  -> true | uu____11045 -> false
  
let (uu___is_Norm_request_requires_rejig : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Norm_request_requires_rejig  -> true
    | uu____11056 -> false
  
let (is_norm_request :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.args -> norm_request_t) =
  fun hd1  ->
    fun args  ->
      let aux min_args =
        let uu____11085 = FStar_All.pipe_right args FStar_List.length  in
        FStar_All.pipe_right uu____11085
          (fun n1  ->
             if n1 < min_args
             then Norm_request_none
             else
               if n1 = min_args
               then Norm_request_ready
               else Norm_request_requires_rejig)
         in
      let uu____11125 =
        let uu____11126 = FStar_Syntax_Util.un_uinst hd1  in
        uu____11126.FStar_Syntax_Syntax.n  in
      match uu____11125 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          -> aux (Prims.parse_int "2")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          aux (Prims.parse_int "1")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          aux (Prims.parse_int "3")
      | uu____11152 -> Norm_request_none
  
let (should_consider_norm_requests : FStar_TypeChecker_Cfg.cfg -> Prims.bool)
  =
  fun cfg  ->
    (Prims.op_Negation
       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
      &&
      (let uu____11231 =
         FStar_Ident.lid_equals
           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
           FStar_Parser_Const.prims_lid
          in
       Prims.op_Negation uu____11231)
  
let (rejig_norm_request :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term)
  =
  fun hd1  ->
    fun args  ->
      let uu____11260 =
        let uu____11261 = FStar_Syntax_Util.un_uinst hd1  in
        uu____11261.FStar_Syntax_Syntax.n  in
      match uu____11260 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          ->
          (match args with
           | t1::t2::rest when
               (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____11362 = FStar_Syntax_Util.mk_app hd1 [t1; t2]  in
               FStar_Syntax_Util.mk_app uu____11362 rest
           | uu____11409 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize_term")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          (match args with
           | t::rest when (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____11476 = FStar_Syntax_Util.mk_app hd1 [t]  in
               FStar_Syntax_Util.mk_app uu____11476 rest
           | uu____11511 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          (match args with
           | t1::t2::t3::rest when
               (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____11628 = FStar_Syntax_Util.mk_app hd1 [t1; t2; t3]
                  in
               FStar_Syntax_Util.mk_app uu____11628 rest
           | uu____11687 ->
               failwith "Impossible! invalid rejig_norm_request for norm")
      | uu____11693 ->
          let uu____11694 =
            let uu____11696 = FStar_Syntax_Print.term_to_string hd1  in
            FStar_String.op_Hat
              "Impossible! invalid rejig_norm_request for: %s" uu____11696
             in
          failwith uu____11694
  
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s  ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
  
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___9_11721  ->
    match uu___9_11721 with
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
        let uu____11728 =
          let uu____11731 =
            let uu____11732 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            FStar_TypeChecker_Env.UnfoldOnly uu____11732  in
          [uu____11731]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____11728
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____11748 =
          let uu____11751 =
            let uu____11752 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            FStar_TypeChecker_Env.UnfoldFully uu____11752  in
          [uu____11751]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____11748
    | FStar_Syntax_Embeddings.UnfoldAttr names1 ->
        let uu____11768 =
          let uu____11771 =
            let uu____11772 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            FStar_TypeChecker_Env.UnfoldAttr uu____11772  in
          [uu____11771]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____11768
    | FStar_Syntax_Embeddings.NBE  -> [FStar_TypeChecker_Env.NBE]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  = fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____11805 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term * 'Auu____11805) Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list * FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____11962 =
            let uu____11967 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____11967 s  in
          match uu____11962 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____11983 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____11983
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
        | uu____12022::(tm,uu____12024)::[] ->
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
        | (tm,uu____12085)::[] ->
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
        | (steps,uu____12130)::uu____12131::(tm,uu____12133)::[] ->
            let add_exclude s z =
              let uu____12207 =
                FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s  in
              if uu____12207
              then s
              else (FStar_TypeChecker_Env.Exclude z) :: s  in
            let uu____12214 =
              let uu____12219 = full_norm steps  in parse_steps uu____12219
               in
            (match uu____12214 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = FStar_TypeChecker_Env.Beta :: s  in
                 let s2 = add_exclude s1 FStar_TypeChecker_Env.Zeta  in
                 let s3 = add_exclude s2 FStar_TypeChecker_Env.Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____12282 -> FStar_Pervasives_Native.None
  
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun s  ->
      fun tm  ->
        let delta_level =
          let uu____12408 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___10_12415  ->
                    match uu___10_12415 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____12417 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____12419 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____12427 -> true
                    | uu____12435 -> false))
             in
          if uu____12408
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta]  in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____12445  ->
             let uu____12446 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____12446);
        (let tm_norm =
           let uu____12458 =
             let uu____12535 = FStar_TypeChecker_Cfg.cfg_env cfg  in
             uu____12535.FStar_TypeChecker_Env.nbe  in
           uu____12458 s cfg.FStar_TypeChecker_Cfg.tcenv tm  in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____12647  ->
              let uu____12648 = FStar_Syntax_Print.term_to_string tm_norm  in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____12648);
         tm_norm)
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___11_12659  ->
    match uu___11_12659 with
    | (App
        (uu____12663,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____12664;
                       FStar_Syntax_Syntax.vars = uu____12665;_},uu____12666,uu____12667))::uu____12668
        -> true
    | uu____12682 -> false
  
let firstn :
  'Auu____12693 .
    Prims.int ->
      'Auu____12693 Prims.list ->
        ('Auu____12693 Prims.list * 'Auu____12693 Prims.list)
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack  ->
      let rec drop_irrel uu___12_12820 =
        match uu___12_12820 with
        | (MemoLazy uu____12825)::s -> drop_irrel s
        | (UnivArgs uu____12839)::s -> drop_irrel s
        | s -> s  in
      let uu____12852 = drop_irrel stack  in
      match uu____12852 with
      | (App
          (uu____12856,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____12857;
                         FStar_Syntax_Syntax.vars = uu____12858;_},uu____12859,uu____12860))::uu____12861
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____12874 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____12919) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____12937) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____12975  ->
                  match uu____12975 with
                  | (a,uu____12990) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____13017 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____13050 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____13057 -> false
    | FStar_Syntax_Syntax.Tm_type uu____13079 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____13081 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____13088 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____13093 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____13095 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____13102 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____13114 -> false
    | FStar_Syntax_Syntax.Tm_let uu____13128 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____13154 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____13190 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____13215 -> true
    | FStar_Syntax_Syntax.Tm_match uu____13232 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____13343  ->
                   match uu____13343 with
                   | (a,uu____13358) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____13377) ->
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
            | FStar_Syntax_Syntax.Meta_pattern (uu____13584,args) ->
                FStar_Util.for_some
                  (FStar_Util.for_some
                     (fun uu____13663  ->
                        match uu____13663 with
                        | (a,uu____13678) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____13695,uu____13696,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____13726,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____13748 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____13758 -> false
            | FStar_Syntax_Syntax.Meta_named uu____13760 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____13775 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____13786 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Should_unfold_fully  -> true
    | uu____13797 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Should_unfold_reify  -> true
    | uu____13808 -> false
  
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
            let uu____13991 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo
               in
            match uu____13991 with
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
              (fun uu____14214  ->
                 fun uu____14215  ->
                   match (uu____14214, uu____14215) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____14321 =
            match uu____14321 with
            | (x,y,z) ->
                let uu____14341 = FStar_Util.string_of_bool x  in
                let uu____14343 = FStar_Util.string_of_bool y  in
                let uu____14345 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____14341 uu____14343
                  uu____14345
             in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg  in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____14373  ->
                    let uu____14374 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____14376 = FStar_Util.string_of_bool b  in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____14374 uu____14376);
               if b then reif else no)
            else
              if
                (let uu____14391 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                 FStar_Option.isSome uu____14391)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____14420  ->
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
                          ((is_rec,uu____14476),uu____14477);
                        FStar_Syntax_Syntax.sigrng = uu____14478;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____14480;
                        FStar_Syntax_Syntax.sigattrs = uu____14481;_},uu____14482),uu____14483),uu____14484,uu____14485,uu____14486)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____14686  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____14688,uu____14689,uu____14690,uu____14691) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____14804  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____14807),uu____14808);
                        FStar_Syntax_Syntax.sigrng = uu____14809;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____14811;
                        FStar_Syntax_Syntax.sigattrs = uu____14812;_},uu____14813),uu____14814),uu____14815,uu____14816,uu____14817)
                     when
                     is_rec &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____15017  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____15019,FStar_Pervasives_Native.Some
                    uu____15020,uu____15021,uu____15022) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____15136  ->
                           let uu____15137 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____15137);
                      (let uu____15140 =
                         let uu____15152 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____15190 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____15190
                            in
                         let uu____15206 =
                           let uu____15218 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____15256 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____15256
                              in
                           let uu____15288 =
                             let uu____15300 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____15338 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____15338
                                in
                             [uu____15300]  in
                           uu____15218 :: uu____15288  in
                         uu____15152 :: uu____15206  in
                       comb_or uu____15140))
                 | (uu____15390,uu____15391,FStar_Pervasives_Native.Some
                    uu____15392,uu____15393) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____15507  ->
                           let uu____15508 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____15508);
                      (let uu____15511 =
                         let uu____15523 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____15561 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____15561
                            in
                         let uu____15577 =
                           let uu____15589 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____15627 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____15627
                              in
                           let uu____15659 =
                             let uu____15671 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____15709 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____15709
                                in
                             [uu____15671]  in
                           uu____15589 :: uu____15659  in
                         uu____15523 :: uu____15577  in
                       comb_or uu____15511))
                 | (uu____15761,uu____15762,uu____15763,FStar_Pervasives_Native.Some
                    uu____15764) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____15878  ->
                           let uu____15879 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____15879);
                      (let uu____15882 =
                         let uu____15894 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____15932 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____15932
                            in
                         let uu____15948 =
                           let uu____15960 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____15998 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____15998
                              in
                           let uu____16030 =
                             let uu____16042 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____16080 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____16080
                                in
                             [uu____16042]  in
                           uu____15960 :: uu____16030  in
                         uu____15894 :: uu____15948  in
                       comb_or uu____15882))
                 | uu____16132 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____16199  ->
                           let uu____16200 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____16202 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____16204 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level
                              in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____16200 uu____16202 uu____16204);
                      (let uu____16207 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___13_16213  ->
                                 match uu___13_16213 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.InliningDelta  ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                     uu____16217 -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____16221 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv
                                        in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____16221 l))
                          in
                       FStar_All.pipe_left yesno uu____16207)))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____16237  ->
               let uu____16238 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____16240 =
                 let uu____16242 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____16242  in
               let uu____16243 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____16238 uu____16240 uu____16243);
          (match res with
           | (false ,uu____16246,uu____16247) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____16272 ->
               let uu____16282 =
                 let uu____16284 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____16284
                  in
               FStar_All.pipe_left failwith uu____16282)
  
let decide_unfolding :
  'Auu____16303 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'Auu____16303 ->
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
                    let uu___1160_16728 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___1162_16801 =
                           cfg.FStar_TypeChecker_Cfg.steps  in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1162_16801.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1162_16801.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1162_16801.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1162_16801.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1162_16801.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1162_16801.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1162_16801.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___1162_16801.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1162_16801.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1162_16801.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1162_16801.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1162_16801.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1162_16801.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1162_16801.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1162_16801.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1162_16801.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1162_16801.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1162_16801.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___1162_16801.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1162_16801.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1162_16801.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1162_16801.FStar_TypeChecker_Cfg.for_extraction)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1160_16728.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1160_16728.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___1160_16728.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1160_16728.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1160_16728.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1160_16728.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1160_16728.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1160_16728.FStar_TypeChecker_Cfg.reifying)
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
                        let uu____16997 = push1 e t  in (UnivArgs (us, r)) ::
                          uu____16997
                    | h::t -> e :: h :: t  in
                  let ref =
                    let uu____17017 =
                      let uu____17024 =
                        let uu____17025 =
                          let uu____17026 = FStar_Syntax_Syntax.lid_of_fv fv
                             in
                          FStar_Const.Const_reflect uu____17026  in
                        FStar_Syntax_Syntax.Tm_constant uu____17025  in
                      FStar_Syntax_Syntax.mk uu____17024  in
                    uu____17017 FStar_Pervasives_Native.None
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
    let uu____17224 =
      let uu____17225 = FStar_Syntax_Subst.compress t  in
      uu____17225.FStar_Syntax_Syntax.n  in
    match uu____17224 with
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____17284 =
          let uu____17285 = FStar_Syntax_Util.un_uinst hd1  in
          uu____17285.FStar_Syntax_Syntax.n  in
        (match uu____17284 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStar_List.length args) = (Prims.parse_int "3"))
             ->
             let f =
               let uu____17329 =
                 let uu____17340 =
                   let uu____17355 = FStar_All.pipe_right args FStar_List.tl
                      in
                   FStar_All.pipe_right uu____17355 FStar_List.tl  in
                 FStar_All.pipe_right uu____17340 FStar_List.hd  in
               FStar_All.pipe_right uu____17329 FStar_Pervasives_Native.fst
                in
             FStar_Pervasives_Native.Some f
         | uu____17510 -> FStar_Pervasives_Native.None)
    | uu____17515 -> FStar_Pervasives_Native.None
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____18472 ->
                   let uu____18503 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____18503
               | uu____18506 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____18516  ->
               let uu____18517 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____18519 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____18521 = FStar_Syntax_Print.term_to_string t1  in
               let uu____18523 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____18531 =
                 let uu____18533 =
                   let uu____18536 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____18536
                    in
                 stack_to_string uu____18533  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____18517 uu____18519 uu____18521 uu____18523 uu____18531);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____18564  ->
               let uu____18565 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____18565);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____18575  ->
                     let uu____18576 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____18576);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____18579 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____18583  ->
                     let uu____18584 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____18584);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____18587 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____18596  ->
                     let uu____18597 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____18597);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____18600 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____18608  ->
                     let uu____18609 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____18609);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____18612;
                 FStar_Syntax_Syntax.fv_delta = uu____18613;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____18617  ->
                     let uu____18618 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____18618);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____18621;
                 FStar_Syntax_Syntax.fv_delta = uu____18622;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____18623);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____18639  ->
                     let uu____18640 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____18640);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid
                  in
               let uu____18657 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
               (match uu____18657 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level _18664) when
                    _18664 = (Prims.parse_int "0") ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____18668  ->
                          let uu____18669 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____18669);
                     rebuild cfg env stack t1)
                | uu____18672 ->
                    let uu____18675 =
                      decide_unfolding cfg env stack
                        t1.FStar_Syntax_Syntax.pos fv qninfo
                       in
                    (match uu____18675 with
                     | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                         do_unfold_fv cfg1 env stack1 t1 qninfo fv
                     | FStar_Pervasives_Native.None  ->
                         rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_quoted uu____18881 ->
               let uu____18894 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____18894
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____18946 = is_norm_request hd1 args  in
                  uu____18946 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu____18952 = rejig_norm_request hd1 args  in
                 norm cfg env stack uu____18952))
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____19004 = is_norm_request hd1 args  in
                  uu____19004 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___1270_19081 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1272_19154 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1272_19154.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1272_19154.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1272_19154.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___1272_19154.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1272_19154.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1272_19154.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1272_19154.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1272_19154.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1272_19154.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1272_19154.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1272_19154.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1272_19154.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1272_19154.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1272_19154.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1272_19154.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1272_19154.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1272_19154.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1272_19154.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1272_19154.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1272_19154.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1272_19154.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1272_19154.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1272_19154.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1270_19081.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1270_19081.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1270_19081.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1270_19081.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1270_19081.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1270_19081.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____19221 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____19221 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____19273  ->
                                 fun stack1  ->
                                   match uu____19273 with
                                   | (a,aq) ->
                                       let uu____19297 =
                                         let uu____19298 =
                                           let uu____19305 =
                                             let uu____19306 =
                                               let uu____19346 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____19346, false)
                                                in
                                             Clos uu____19306  in
                                           (uu____19305, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____19298  in
                                       uu____19297 :: stack1) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____19434  ->
                            let uu____19435 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____19435);
                       norm cfg env stack1 hd1))
                 | FStar_Pervasives_Native.Some (s,tm) when is_nbe_request s
                     ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____19478 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting NBE request on %s ... \n" uu____19478)
                      else ();
                      (let tm' = closure_as_term cfg env tm  in
                       let start = FStar_Util.now ()  in
                       let tm_norm = nbe_eval cfg s tm'  in
                       let fin = FStar_Util.now ()  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         (let uu____19505 =
                            let uu____19507 =
                              let uu____19509 =
                                FStar_Util.time_diff start fin  in
                              FStar_Pervasives_Native.snd uu____19509  in
                            FStar_Util.string_of_int uu____19507  in
                          let uu____19516 =
                            FStar_Syntax_Print.term_to_string tm'  in
                          let uu____19518 =
                            FStar_Syntax_Print.term_to_string tm_norm  in
                          FStar_Util.print3 "NBE'd (%s ms) %s\n\tto %s\n"
                            uu____19505 uu____19516 uu____19518)
                       else ();
                       norm cfg env stack tm_norm))
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____19549 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting norm request on %s ... \n" uu____19549)
                      else ();
                      (let delta_level =
                         let uu____19557 =
                           FStar_All.pipe_right s
                             (FStar_Util.for_some
                                (fun uu___14_19564  ->
                                   match uu___14_19564 with
                                   | FStar_TypeChecker_Env.UnfoldUntil
                                       uu____19566 -> true
                                   | FStar_TypeChecker_Env.UnfoldOnly
                                       uu____19568 -> true
                                   | FStar_TypeChecker_Env.UnfoldFully
                                       uu____19576 -> true
                                   | uu____19584 -> false))
                            in
                         if uu____19557
                         then
                           [FStar_TypeChecker_Env.Unfold
                              FStar_Syntax_Syntax.delta_constant]
                         else [FStar_TypeChecker_Env.NoDelta]  in
                       let cfg'1 =
                         let uu___1313_19662 = cfg  in
                         let uu____19733 =
                           let uu___1315_19786 =
                             FStar_TypeChecker_Cfg.to_fsteps s  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.unfold_only);
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               true;
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___1315_19786.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         {
                           FStar_TypeChecker_Cfg.steps = uu____19733;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___1313_19662.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___1313_19662.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = delta_level;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___1313_19662.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong =
                             (uu___1313_19662.FStar_TypeChecker_Cfg.strong);
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___1313_19662.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___1313_19662.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let stack' =
                         let tail1 = (Cfg cfg) :: stack  in
                         if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           let uu____19846 =
                             let uu____19847 =
                               let uu____19856 = FStar_Util.now ()  in
                               (t1, uu____19856)  in
                             Debug uu____19847  in
                           uu____19846 :: tail1
                         else tail1  in
                       norm cfg'1 env stack' tm))))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____19865 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____19865
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____19896 =
                      let uu____19903 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____19903, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____19896  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____19917 = lookup_bvar env x  in
               (match uu____19917 with
                | Univ uu____19922 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                    then
                      let uu____20004 = FStar_ST.op_Bang r  in
                      (match uu____20004 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____20128  ->
                                 let uu____20129 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____20131 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____20129
                                   uu____20131);
                            (let uu____20134 = maybe_weakly_reduced t'  in
                             if uu____20134
                             then
                               match stack with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____20145 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____20229)::uu____20230 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____20245,uu____20246))::stack_rest ->
                    (match c with
                     | Univ uu____20254 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____20263 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____20321  ->
                                    let uu____20322 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____20322);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____20373  ->
                                    let uu____20374 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____20374);
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
                       (fun uu____20493  ->
                          let uu____20494 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____20494);
                     norm cfg env stack1 t1)
                | (Match uu____20497)::uu____20498 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____20560 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____20560 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____20622  -> dummy :: env1) env)
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
                                          let uu____20719 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____20719)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1433_20750 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1433_20750.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1433_20750.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____20765 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____20778  ->
                                 let uu____20779 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____20779);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1440_20869 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1440_20869.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1440_20869.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1440_20869.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1440_20869.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1440_20869.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1440_20869.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1440_20869.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1440_20869.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____20950)::uu____20951 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____20978 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____20978 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____21040  -> dummy :: env1) env)
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
                                          let uu____21137 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____21137)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1433_21168 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1433_21168.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1433_21168.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____21183 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____21196  ->
                                 let uu____21197 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____21197);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1440_21287 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1440_21287.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1440_21287.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1440_21287.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1440_21287.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1440_21287.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1440_21287.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1440_21287.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1440_21287.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____21368)::uu____21369 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____21394 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____21394 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____21456  -> dummy :: env1) env)
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
                                          let uu____21553 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____21553)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1433_21584 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1433_21584.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1433_21584.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____21599 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____21612  ->
                                 let uu____21613 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____21613);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1440_21703 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1440_21703.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1440_21703.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1440_21703.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1440_21703.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1440_21703.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1440_21703.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1440_21703.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1440_21703.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____21784)::uu____21785 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____21819 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____21819 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____21881  -> dummy :: env1) env)
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
                                          let uu____21978 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____21978)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1433_22009 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1433_22009.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1433_22009.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____22024 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____22037  ->
                                 let uu____22038 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____22038);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1440_22128 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1440_22128.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1440_22128.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1440_22128.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1440_22128.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1440_22128.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1440_22128.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1440_22128.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1440_22128.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____22209)::uu____22210 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____22241 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____22241 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____22303  -> dummy :: env1) env)
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
                                          let uu____22400 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____22400)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1433_22431 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1433_22431.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1433_22431.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____22446 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____22459  ->
                                 let uu____22460 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____22460);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1440_22550 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1440_22550.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1440_22550.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1440_22550.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1440_22550.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1440_22550.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1440_22550.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1440_22550.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1440_22550.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____22631)::uu____22632 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____22670 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____22670 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____22732  -> dummy :: env1) env)
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
                                          let uu____22829 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____22829)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1433_22860 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1433_22860.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1433_22860.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____22875 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____22888  ->
                                 let uu____22889 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____22889);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1440_22979 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1440_22979.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1440_22979.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1440_22979.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1440_22979.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1440_22979.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1440_22979.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1440_22979.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1440_22979.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____23076 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____23076 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____23138  -> dummy :: env1) env)
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
                                          let uu____23235 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____23235)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1433_23266 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1433_23266.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1433_23266.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____23281 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____23294  ->
                                 let uu____23295 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____23295);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1440_23385 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1440_23385.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1440_23385.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1440_23385.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1440_23385.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1440_23385.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1440_23385.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1440_23385.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1440_23385.FStar_TypeChecker_Cfg.reifying)
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
                      (fun uu____23526  ->
                         fun stack1  ->
                           match uu____23526 with
                           | (a,aq) ->
                               let uu____23550 =
                                 let uu____23551 =
                                   let uu____23558 =
                                     let uu____23559 =
                                       let uu____23599 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____23599, false)  in
                                     Clos uu____23559  in
                                   (uu____23558, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____23551  in
                               uu____23550 :: stack1) args)
                  in
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____23687  ->
                     let uu____23688 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____23688);
                norm cfg env stack1 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,uu____23706) when
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
                             ((let uu___1467_23820 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1467_23820.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1467_23820.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____23831 ->
                      let uu____23846 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____23846)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____23866 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____23866 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____23944 =
                          let uu____23945 =
                            let uu____23961 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___1476_23984 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1476_23984.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___1476_23984.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____23961)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____23945  in
                        mk uu____23944 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____24040 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____24040
               else
                 (let uu____24051 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____24051 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____24083 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____24119  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____24083 c1  in
                      let t2 =
                        let uu____24156 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____24156 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____24382)::uu____24383 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____24431  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____24433)::uu____24434 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____24445  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____24447,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____24448;
                                   FStar_Syntax_Syntax.vars = uu____24449;_},uu____24450,uu____24451))::uu____24452
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____24467  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____24469)::uu____24470 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____24485  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____24487 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____24490  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____24503  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____24557 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____24557
                         | FStar_Util.Inr c ->
                             let uu____24599 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____24599
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____24697 =
                               let uu____24698 =
                                 let uu____24745 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____24745, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____24698
                                in
                             mk uu____24697 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____24820 ->
                           let uu____24821 =
                             let uu____24830 =
                               let uu____24831 =
                                 let uu____24878 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____24878, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____24831
                                in
                             mk uu____24830 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____24821))))
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
                   let uu___1555_25135 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1557_25208 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1557_25208.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1555_25135.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1555_25135.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___1555_25135.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1555_25135.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1555_25135.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1555_25135.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___1555_25135.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1555_25135.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____25372 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____25372 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___1570_25475 = cfg  in
                               let uu____25546 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1570_25475.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____25546;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1570_25475.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1570_25475.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1570_25475.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___1570_25475.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1570_25475.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1570_25475.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1570_25475.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____25673 =
                                 let uu____25682 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____25682  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____25673
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___1577_25709 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1577_25709.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1577_25709.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1577_25709.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1577_25709.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____25724 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____25724
           | FStar_Syntax_Syntax.Tm_let
               ((uu____25763,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____25764;
                               FStar_Syntax_Syntax.lbunivs = uu____25765;
                               FStar_Syntax_Syntax.lbtyp = uu____25766;
                               FStar_Syntax_Syntax.lbeff = uu____25767;
                               FStar_Syntax_Syntax.lbdef = uu____25768;
                               FStar_Syntax_Syntax.lbattrs = uu____25769;
                               FStar_Syntax_Syntax.lbpos = uu____25770;_}::uu____25771),uu____25772)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name
                   cfg.FStar_TypeChecker_Cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____25934 =
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
               if uu____25934
               then
                 let binder =
                   let uu____25942 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____25942  in
                 let env1 =
                   let uu____25970 =
                     let uu____25977 =
                       let uu____25978 =
                         let uu____26018 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____26018,
                           false)
                          in
                       Clos uu____25978  in
                     ((FStar_Pervasives_Native.Some binder), uu____25977)  in
                   uu____25970 :: env  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____26113  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                 then
                   (FStar_TypeChecker_Cfg.log cfg
                      (fun uu____26124  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____26126 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____26126))
                 else
                   (let uu____26137 =
                      let uu____26146 =
                        let uu____26147 =
                          let uu____26159 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____26159
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____26147]  in
                      FStar_Syntax_Subst.open_term uu____26146 body  in
                    match uu____26137 with
                    | (bs,body1) ->
                        (FStar_TypeChecker_Cfg.log cfg
                           (fun uu____26249  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____26284 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____26284  in
                            FStar_Util.Inl
                              (let uu___1619_26323 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1619_26323.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1619_26323.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____26336  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___1624_26353 = lb  in
                             let uu____26368 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1624_26353.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1624_26353.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____26368;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1624_26353.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1624_26353.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____26415  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___1631_26515 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps =
                                 (uu___1631_26515.FStar_TypeChecker_Cfg.steps);
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___1631_26515.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___1631_26515.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 (uu___1631_26515.FStar_TypeChecker_Cfg.delta_level);
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___1631_26515.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong = true;
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___1631_26515.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___1631_26515.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___1631_26515.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           FStar_TypeChecker_Cfg.log cfg1
                             (fun uu____26589  ->
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
               let uu____26646 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____26646 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____26763 =
                               let uu___1647_26774 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1647_26774.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1647_26774.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____26763  in
                           let uu____26801 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____26801 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____26867 =
                                   FStar_List.map (fun uu____26890  -> dummy)
                                     lbs1
                                    in
                                 let uu____26898 =
                                   let uu____26907 =
                                     FStar_List.map
                                       (fun uu____26934  -> dummy) xs1
                                      in
                                   FStar_List.append uu____26907 env  in
                                 FStar_List.append uu____26867 uu____26898
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____27001 =
                                       let uu___1661_27016 = rc  in
                                       let uu____27031 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1661_27016.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____27031;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1661_27016.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____27001
                                 | uu____27059 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___1666_27080 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1666_27080.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1666_27080.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1666_27080.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1666_27080.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____27104 =
                        FStar_List.map (fun uu____27127  -> dummy) lbs2  in
                      FStar_List.append uu____27104 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____27150 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____27150 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___1675_27211 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___1675_27211.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1675_27211.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
               ->
               let uu____27293 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____27293
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____27344 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____27437  ->
                        match uu____27437 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___1691_27595 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1691_27595.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___1691_27595.FStar_Syntax_Syntax.sort)
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
               (match uu____27344 with
                | (rec_env,memos,uu____27878) ->
                    let uu____27941 =
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
                             let uu____28257 =
                               let uu____28264 =
                                 let uu____28265 =
                                   let uu____28305 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____28305, false)
                                    in
                                 Clos uu____28265  in
                               (FStar_Pervasives_Native.None, uu____28264)
                                in
                             uu____28257 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____28425  ->
                     let uu____28426 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____28426);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____28526 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____28538::uu____28539 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____28548) ->
                                 norm cfg env ((Meta (env, m, r)) :: stack)
                                   head1
                             | FStar_Syntax_Syntax.Meta_pattern (names1,args)
                                 ->
                                 let args1 = norm_pattern_args cfg env args
                                    in
                                 let names2 =
                                   FStar_All.pipe_right names1
                                     (FStar_List.map (norm cfg env []))
                                    in
                                 norm cfg env
                                   ((Meta
                                       (env,
                                         (FStar_Syntax_Syntax.Meta_pattern
                                            (names2, args1)),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____28675 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern
                                  (names1,args) ->
                                  let names2 =
                                    FStar_All.pipe_right names1
                                      (FStar_List.map (norm cfg env []))
                                     in
                                  let uu____28767 =
                                    let uu____28796 =
                                      norm_pattern_args cfg env args  in
                                    (names2, uu____28796)  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____28767
                              | uu____28837 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____28855 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____28895 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____28929 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____28955 =
                        let uu____28957 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____28959 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____28957 uu____28959
                         in
                      failwith uu____28955
                    else
                      (let uu____28968 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____28968)
                | uu____28977 -> norm cfg env stack t2))

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
              let uu____29032 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____29032 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____29062  ->
                        let uu____29063 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____29063);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____29088  ->
                        let uu____29089 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____29091 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____29089 uu____29091);
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
                      | (UnivArgs (us',uu____29126))::stack1 ->
                          ((let uu____29135 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____29135
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____29143 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____29143) us'
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
                      | uu____29179 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____29182 ->
                          let uu____29185 =
                            let uu____29187 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____29187
                             in
                          failwith uu____29185
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
                  let uu___1803_29395 = cfg  in
                  let uu____29466 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____29466;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___1803_29395.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___1803_29395.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only false];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___1803_29395.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___1803_29395.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___1803_29395.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___1803_29395.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___1803_29395.FStar_TypeChecker_Cfg.reifying)
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
                     (uu____29695,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____29696;
                                    FStar_Syntax_Syntax.vars = uu____29697;_},uu____29698,uu____29699))::uu____29700
                     -> ()
                 | uu____29713 ->
                     let uu____29716 =
                       let uu____29718 = stack_to_string stack  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____29718
                        in
                     failwith uu____29716);
                (let head0 = head1  in
                 let head2 = FStar_Syntax_Util.unascribe head1  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____29743  ->
                      let uu____29744 = FStar_Syntax_Print.tag_of_term head2
                         in
                      let uu____29746 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____29744
                        uu____29746);
                 (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                  let uu____29758 =
                    let uu____29759 = FStar_Syntax_Subst.compress head3  in
                    uu____29759.FStar_Syntax_Syntax.n  in
                  match uu____29758 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let ed =
                        let uu____29875 =
                          FStar_TypeChecker_Env.norm_eff_name
                            cfg.FStar_TypeChecker_Cfg.tcenv m
                           in
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv uu____29875
                         in
                      let uu____29884 = ed.FStar_Syntax_Syntax.bind_repr  in
                      (match uu____29884 with
                       | (uu____29889,bind_repr) ->
                           (match lb.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____29915 ->
                                failwith
                                  "Cannot reify a top-level let binding"
                            | FStar_Util.Inl x ->
                                let is_return e =
                                  let uu____29966 =
                                    let uu____29967 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____29967.FStar_Syntax_Syntax.n  in
                                  match uu____29966 with
                                  | FStar_Syntax_Syntax.Tm_meta
                                      (e1,FStar_Syntax_Syntax.Meta_monadic
                                       (uu____29985,uu____29986))
                                      ->
                                      let uu____30019 =
                                        let uu____30020 =
                                          FStar_Syntax_Subst.compress e1  in
                                        uu____30020.FStar_Syntax_Syntax.n  in
                                      (match uu____30019 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                            (uu____30038,msrc,uu____30040))
                                           when
                                           FStar_Syntax_Util.is_pure_effect
                                             msrc
                                           ->
                                           let uu____30081 =
                                             FStar_Syntax_Subst.compress e2
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____30081
                                       | uu____30094 ->
                                           FStar_Pervasives_Native.None)
                                  | uu____30099 ->
                                      FStar_Pervasives_Native.None
                                   in
                                let uu____30104 =
                                  is_return lb.FStar_Syntax_Syntax.lbdef  in
                                (match uu____30104 with
                                 | FStar_Pervasives_Native.Some e ->
                                     let lb1 =
                                       let uu___1875_30139 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___1875_30139.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___1875_30139.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           (uu___1875_30139.FStar_Syntax_Syntax.lbtyp);
                                         FStar_Syntax_Syntax.lbeff =
                                           FStar_Parser_Const.effect_PURE_lid;
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___1875_30139.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___1875_30139.FStar_Syntax_Syntax.lbpos)
                                       }  in
                                     let uu____30154 = FStar_List.tl stack
                                        in
                                     let uu____30155 =
                                       let uu____30164 =
                                         let uu____30171 =
                                           let uu____30172 =
                                             let uu____30197 =
                                               FStar_Syntax_Util.mk_reify
                                                 body
                                                in
                                             ((false, [lb1]), uu____30197)
                                              in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____30172
                                            in
                                         FStar_Syntax_Syntax.mk uu____30171
                                          in
                                       uu____30164
                                         FStar_Pervasives_Native.None
                                         head3.FStar_Syntax_Syntax.pos
                                        in
                                     norm cfg env uu____30154 uu____30155
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____30257 =
                                       let uu____30259 = is_return body  in
                                       match uu____30259 with
                                       | FStar_Pervasives_Native.Some
                                           {
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_bvar y;
                                             FStar_Syntax_Syntax.pos =
                                               uu____30268;
                                             FStar_Syntax_Syntax.vars =
                                               uu____30269;_}
                                           -> FStar_Syntax_Syntax.bv_eq x y
                                       | uu____30285 -> false  in
                                     if uu____30257
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
                                          let uu____30375 =
                                            let uu____30382 =
                                              let uu____30383 =
                                                let uu____30418 =
                                                  let uu____30432 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____30432]  in
                                                (uu____30418, body1,
                                                  (FStar_Pervasives_Native.Some
                                                     body_rc))
                                                 in
                                              FStar_Syntax_Syntax.Tm_abs
                                                uu____30383
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____30382
                                             in
                                          uu____30375
                                            FStar_Pervasives_Native.None
                                            body1.FStar_Syntax_Syntax.pos
                                           in
                                        let close1 = closure_as_term cfg env
                                           in
                                        let bind_inst =
                                          let uu____30525 =
                                            let uu____30526 =
                                              FStar_Syntax_Subst.compress
                                                bind_repr
                                               in
                                            uu____30526.FStar_Syntax_Syntax.n
                                             in
                                          match uu____30525 with
                                          | FStar_Syntax_Syntax.Tm_uinst
                                              (bind1,uu____30544::uu____30545::[])
                                              ->
                                              let uu____30558 =
                                                let uu____30565 =
                                                  let uu____30566 =
                                                    let uu____30577 =
                                                      let uu____30578 =
                                                        let uu____30579 =
                                                          close1
                                                            lb.FStar_Syntax_Syntax.lbtyp
                                                           in
                                                        (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.FStar_TypeChecker_Cfg.tcenv
                                                          uu____30579
                                                         in
                                                      let uu____30588 =
                                                        let uu____30591 =
                                                          let uu____30592 =
                                                            close1 t  in
                                                          (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                            cfg.FStar_TypeChecker_Cfg.tcenv
                                                            uu____30592
                                                           in
                                                        [uu____30591]  in
                                                      uu____30578 ::
                                                        uu____30588
                                                       in
                                                    (bind1, uu____30577)  in
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                    uu____30566
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____30565
                                                 in
                                              uu____30558
                                                FStar_Pervasives_Native.None
                                                rng
                                          | uu____30607 ->
                                              failwith
                                                "NIY : Reification of indexed effects"
                                           in
                                        let maybe_range_arg =
                                          let uu____30630 =
                                            FStar_Util.for_some
                                              (FStar_Syntax_Util.attr_eq
                                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                                              ed.FStar_Syntax_Syntax.eff_attrs
                                             in
                                          if uu____30630
                                          then
                                            let uu____30651 =
                                              let uu____30664 =
                                                FStar_TypeChecker_Cfg.embed_simple
                                                  FStar_Syntax_Embeddings.e_range
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____30664
                                               in
                                            let uu____30673 =
                                              let uu____30688 =
                                                let uu____30701 =
                                                  FStar_TypeChecker_Cfg.embed_simple
                                                    FStar_Syntax_Embeddings.e_range
                                                    body2.FStar_Syntax_Syntax.pos
                                                    body2.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Syntax_Syntax.as_arg
                                                  uu____30701
                                                 in
                                              [uu____30688]  in
                                            uu____30651 :: uu____30673
                                          else []  in
                                        let reified =
                                          let uu____30771 =
                                            let uu____30778 =
                                              let uu____30779 =
                                                let uu____30804 =
                                                  let uu____30819 =
                                                    let uu____30834 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        lb.FStar_Syntax_Syntax.lbtyp
                                                       in
                                                    let uu____30847 =
                                                      let uu____30862 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          t
                                                         in
                                                      [uu____30862]  in
                                                    uu____30834 ::
                                                      uu____30847
                                                     in
                                                  let uu____30911 =
                                                    let uu____30926 =
                                                      let uu____30941 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          FStar_Syntax_Syntax.tun
                                                         in
                                                      let uu____30954 =
                                                        let uu____30969 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            head4
                                                           in
                                                        let uu____30982 =
                                                          let uu____30997 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          let uu____31010 =
                                                            let uu____31025 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                body2
                                                               in
                                                            [uu____31025]  in
                                                          uu____30997 ::
                                                            uu____31010
                                                           in
                                                        uu____30969 ::
                                                          uu____30982
                                                         in
                                                      uu____30941 ::
                                                        uu____30954
                                                       in
                                                    FStar_List.append
                                                      maybe_range_arg
                                                      uu____30926
                                                     in
                                                  FStar_List.append
                                                    uu____30819 uu____30911
                                                   in
                                                (bind_inst, uu____30804)  in
                                              FStar_Syntax_Syntax.Tm_app
                                                uu____30779
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____30778
                                             in
                                          uu____30771
                                            FStar_Pervasives_Native.None rng
                                           in
                                        FStar_TypeChecker_Cfg.log cfg
                                          (fun uu____31146  ->
                                             let uu____31147 =
                                               FStar_Syntax_Print.term_to_string
                                                 head0
                                                in
                                             let uu____31149 =
                                               FStar_Syntax_Print.term_to_string
                                                 reified
                                                in
                                             FStar_Util.print2
                                               "Reified (1) <%s> to %s\n"
                                               uu____31147 uu____31149);
                                        (let uu____31152 =
                                           FStar_List.tl stack  in
                                         norm cfg env uu____31152 reified)))))
                  | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                      ((let uu____31196 = FStar_Options.defensive ()  in
                        if uu____31196
                        then
                          let is_arg_impure uu____31215 =
                            match uu____31215 with
                            | (e,q) ->
                                let uu____31241 =
                                  let uu____31242 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____31242.FStar_Syntax_Syntax.n  in
                                (match uu____31241 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____31298 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____31298
                                 | uu____31300 -> false)
                             in
                          let uu____31302 =
                            let uu____31304 =
                              let uu____31319 =
                                FStar_Syntax_Syntax.as_arg head_app  in
                              uu____31319 :: args  in
                            FStar_Util.for_some is_arg_impure uu____31304  in
                          (if uu____31302
                           then
                             let uu____31357 =
                               let uu____31363 =
                                 let uu____31365 =
                                   FStar_Syntax_Print.term_to_string head3
                                    in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____31365
                                  in
                               (FStar_Errors.Warning_Defensive, uu____31363)
                                in
                             FStar_Errors.log_issue
                               head3.FStar_Syntax_Syntax.pos uu____31357
                           else ())
                        else ());
                       (let fallback1 uu____31382 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____31386  ->
                               let uu____31387 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____31387 "");
                          (let uu____31391 = FStar_List.tl stack  in
                           let uu____31392 = FStar_Syntax_Util.mk_reify head3
                              in
                           norm cfg env uu____31391 uu____31392)
                           in
                        let fallback2 uu____31410 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____31414  ->
                               let uu____31415 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____31415 "");
                          (let uu____31419 = FStar_List.tl stack  in
                           let uu____31420 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (head3,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               head0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env uu____31419 uu____31420)
                           in
                        let uu____31445 =
                          let uu____31446 =
                            FStar_Syntax_Util.un_uinst head_app  in
                          uu____31446.FStar_Syntax_Syntax.n  in
                        match uu____31445 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____31475 =
                              let uu____31477 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____31477  in
                            if uu____31475
                            then fallback1 ()
                            else
                              (let uu____31486 =
                                 let uu____31488 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____31488  in
                               if uu____31486
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____31529 =
                                      let uu____31534 =
                                        FStar_Syntax_Util.mk_reify head_app
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____31534 args
                                       in
                                    uu____31529 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____31543 = FStar_List.tl stack  in
                                  norm cfg env uu____31543 t1))
                        | uu____31544 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____31546) ->
                      do_reify_monadic fallback cfg env stack e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____31626 = closure_as_term cfg env t'  in
                        reify_lift cfg e msrc mtgt uu____31626  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____31638  ->
                            let uu____31639 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____31639);
                       (let uu____31642 = FStar_List.tl stack  in
                        norm cfg env uu____31642 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                      let branches1 =
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun uu____31848  ->
                                match uu____31848 with
                                | (pat,wopt,tm) ->
                                    let uu____31937 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____31937)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                          head3.FStar_Syntax_Syntax.pos
                         in
                      let uu____32011 = FStar_List.tl stack  in
                      norm cfg env uu____32011 tm
                  | uu____32012 -> fallback ()))

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
              (fun uu____32189  ->
                 let uu____32190 = FStar_Ident.string_of_lid msrc  in
                 let uu____32192 = FStar_Ident.string_of_lid mtgt  in
                 let uu____32194 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____32190
                   uu____32192 uu____32194);
            (let uu____32197 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____32197
             then
               let ed =
                 let uu____32245 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____32245  in
               let uu____32254 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____32254 with
               | (uu____32259,return_repr) ->
                   let return_inst =
                     let uu____32292 =
                       let uu____32293 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____32293.FStar_Syntax_Syntax.n  in
                     match uu____32292 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____32311::[]) ->
                         let uu____32324 =
                           let uu____32331 =
                             let uu____32332 =
                               let uu____32343 =
                                 let uu____32344 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____32344]  in
                               (return_tm, uu____32343)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____32332  in
                           FStar_Syntax_Syntax.mk uu____32331  in
                         uu____32324 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____32351 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____32359 =
                     let uu____32366 =
                       let uu____32367 =
                         let uu____32392 =
                           let uu____32407 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____32420 =
                             let uu____32435 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____32435]  in
                           uu____32407 :: uu____32420  in
                         (return_inst, uu____32392)  in
                       FStar_Syntax_Syntax.Tm_app uu____32367  in
                     FStar_Syntax_Syntax.mk uu____32366  in
                   uu____32359 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____32506 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____32506 with
                | FStar_Pervasives_Native.None  ->
                    let uu____32527 =
                      let uu____32529 = FStar_Ident.text_of_lid msrc  in
                      let uu____32531 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____32529 uu____32531
                       in
                    failwith uu____32527
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____32538;
                      FStar_TypeChecker_Env.mtarget = uu____32539;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____32540;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____32605 =
                      let uu____32607 = FStar_Ident.text_of_lid msrc  in
                      let uu____32609 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____32607 uu____32609
                       in
                    failwith uu____32605
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____32616;
                      FStar_TypeChecker_Env.mtarget = uu____32617;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____32618;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____32712 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____32713 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____32712 t FStar_Syntax_Syntax.tun uu____32713))

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
                (fun uu____32854  ->
                   match uu____32854 with
                   | (a,imp) ->
                       let uu____32889 = norm cfg env [] a  in
                       (uu____32889, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____32950  ->
             let uu____32951 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____32953 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____32951 uu____32953);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____32999 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _33002  -> FStar_Pervasives_Native.Some _33002)
                     uu____32999
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2025_33003 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2025_33003.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2025_33003.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____33053 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _33056  -> FStar_Pervasives_Native.Some _33056)
                     uu____33053
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2036_33057 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2036_33057.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2036_33057.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____33135  ->
                      match uu____33135 with
                      | (a,i) ->
                          let uu____33171 = norm cfg env [] a  in
                          (uu____33171, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___15_33209  ->
                       match uu___15_33209 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____33217 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____33217
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___2053_33241 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2055_33252 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2055_33252.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2053_33241.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2053_33241.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun b  ->
        let uu____33301 = b  in
        match uu____33301 with
        | (x,imp) ->
            let x1 =
              let uu___2063_33329 = x  in
              let uu____33340 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2063_33329.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2063_33329.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____33340
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____33363 =
                    let uu____33364 = closure_as_term cfg env t  in
                    FStar_Syntax_Syntax.Meta uu____33364  in
                  FStar_Pervasives_Native.Some uu____33363
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____33423 =
          FStar_List.fold_left
            (fun uu____33457  ->
               fun b  ->
                 match uu____33457 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____33423 with | (nbs,uu____33537) -> FStar_List.rev nbs

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
            let uu____33632 =
              let uu___2088_33647 = rc  in
              let uu____33662 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2088_33647.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____33662;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2088_33647.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____33632
        | uu____33690 -> lopt

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
            (let uu____33754 = FStar_Syntax_Print.term_to_string tm  in
             let uu____33756 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____33754 uu____33756)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___16_33768  ->
      match uu___16_33768 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____33852 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____33852 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____33876 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____33876)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____33941 = norm_cb cfg  in
            reduce_primops uu____33941 cfg env tm  in
          let uu____33946 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____33946
          then tm1
          else
            (let w t =
               let uu___2116_33989 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2116_33989.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2116_33989.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____34017 =
                 let uu____34018 = FStar_Syntax_Util.unmeta t  in
                 uu____34018.FStar_Syntax_Syntax.n  in
               match uu____34017 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____34044 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____34135)::args1,(bv,uu____34138)::bs1) ->
                   let uu____34237 =
                     let uu____34238 = FStar_Syntax_Subst.compress t  in
                     uu____34238.FStar_Syntax_Syntax.n  in
                   (match uu____34237 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____34256 -> false)
               | ([],[]) -> true
               | (uu____34305,uu____34306) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____34393 = FStar_Syntax_Print.term_to_string t  in
                  let uu____34395 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____34393
                    uu____34395)
               else ();
               (let uu____34400 = FStar_Syntax_Util.head_and_args' t  in
                match uu____34400 with
                | (hd1,args) ->
                    let uu____34468 =
                      let uu____34469 = FStar_Syntax_Subst.compress hd1  in
                      uu____34469.FStar_Syntax_Syntax.n  in
                    (match uu____34468 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____34495 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____34497 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____34499 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____34495 uu____34497 uu____34499)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____34509 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____34550 = FStar_Syntax_Print.term_to_string t  in
                  let uu____34552 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____34550
                    uu____34552)
               else ();
               (let uu____34557 = FStar_Syntax_Util.is_squash t  in
                match uu____34557 with
                | FStar_Pervasives_Native.Some (uu____34577,t') ->
                    is_applied bs t'
                | uu____34601 ->
                    let uu____34614 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____34614 with
                     | FStar_Pervasives_Native.Some (uu____34634,t') ->
                         is_applied bs t'
                     | uu____34658 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____34712 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____34712 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____34723)::(q,uu____34725)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____34804 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____34806 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____34804 uu____34806)
                    else ();
                    (let uu____34811 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____34811 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____34820 =
                           let uu____34821 = FStar_Syntax_Subst.compress p
                              in
                           uu____34821.FStar_Syntax_Syntax.n  in
                         (match uu____34820 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____34849 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____34849))
                          | uu____34873 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____34880)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____34929 =
                           let uu____34930 = FStar_Syntax_Subst.compress p1
                              in
                           uu____34930.FStar_Syntax_Syntax.n  in
                         (match uu____34929 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____34958 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____34958))
                          | uu____34982 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____34998 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____34998 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____35007 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____35007 with
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
                                     let uu____35055 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____35055))
                               | uu____35079 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____35093)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____35142 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____35142 with
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
                                     let uu____35190 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____35190))
                               | uu____35214 -> FStar_Pervasives_Native.None)
                          | uu____35226 -> FStar_Pervasives_Native.None)
                     | uu____35233 -> FStar_Pervasives_Native.None))
               | uu____35240 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____35273 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____35273 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____35283)::[],uu____35284,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____35332 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____35334 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____35332
                         uu____35334)
                    else ();
                    is_quantified_const bv phi')
               | uu____35339 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____35366 =
                 let uu____35367 = FStar_Syntax_Subst.compress phi  in
                 uu____35367.FStar_Syntax_Syntax.n  in
               match uu____35366 with
               | FStar_Syntax_Syntax.Tm_match (uu____35381,br::brs) ->
                   let uu____35500 = br  in
                   (match uu____35500 with
                    | (uu____35529,uu____35530,e) ->
                        let r =
                          let uu____35574 = simp_t e  in
                          match uu____35574 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____35586 =
                                FStar_List.for_all
                                  (fun uu____35616  ->
                                     match uu____35616 with
                                     | (uu____35638,uu____35639,e') ->
                                         let uu____35675 = simp_t e'  in
                                         uu____35675 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____35586
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____35691 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____35713 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____35713
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____35775 =
                 match uu____35775 with
                 | (t1,q) ->
                     let uu____35812 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____35812 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____35868 -> (t1, q))
                  in
               let uu____35889 = FStar_Syntax_Util.head_and_args t  in
               match uu____35889 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____36017 =
                 let uu____36018 = FStar_Syntax_Util.unmeta ty  in
                 uu____36018.FStar_Syntax_Syntax.n  in
               match uu____36017 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____36031) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____36044,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____36097 -> false  in
             let simplify1 arg =
               let uu____36142 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____36142, arg)  in
             let uu____36165 = is_forall_const tm1  in
             match uu____36165 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____36187 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____36189 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____36187
                       uu____36189)
                  else ();
                  (let uu____36194 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____36194))
             | FStar_Pervasives_Native.None  ->
                 let uu____36207 =
                   let uu____36208 = FStar_Syntax_Subst.compress tm1  in
                   uu____36208.FStar_Syntax_Syntax.n  in
                 (match uu____36207 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____36224;
                              FStar_Syntax_Syntax.vars = uu____36225;_},uu____36226);
                         FStar_Syntax_Syntax.pos = uu____36227;
                         FStar_Syntax_Syntax.vars = uu____36228;_},args)
                      ->
                      let uu____36285 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____36285
                      then
                        let uu____36292 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____36292 with
                         | (FStar_Pervasives_Native.Some (true ),uu____36374)::
                             (uu____36375,(arg,uu____36377))::[] ->
                             maybe_auto_squash arg
                         | (uu____36482,(arg,uu____36484))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____36485)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____36590)::uu____36591::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____36685::(FStar_Pervasives_Native.Some (false
                                         ),uu____36686)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____36780 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____36802 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____36802
                         then
                           let uu____36809 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____36809 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____36891)::uu____36892::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____36986::(FStar_Pervasives_Native.Some (true
                                           ),uu____36987)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____37081)::(uu____37082,(arg,uu____37084))::[]
                               -> maybe_auto_squash arg
                           | (uu____37189,(arg,uu____37191))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____37192)::[]
                               -> maybe_auto_squash arg
                           | uu____37297 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____37319 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____37319
                            then
                              let uu____37326 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____37326 with
                              | uu____37408::(FStar_Pervasives_Native.Some
                                              (true ),uu____37409)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____37503)::uu____37504::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____37598)::(uu____37599,(arg,uu____37601))::[]
                                  -> maybe_auto_squash arg
                              | (uu____37706,(p,uu____37708))::(uu____37709,
                                                                (q,uu____37711))::[]
                                  ->
                                  let uu____37819 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____37819
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____37828 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____37850 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____37850
                               then
                                 let uu____37857 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____37857 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____37939)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____37940)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____38042)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____38043)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____38145)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____38146)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____38248)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____38249)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____38351,(arg,uu____38353))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____38354)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____38459)::(uu____38460,(arg,uu____38462))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____38567,(arg,uu____38569))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____38570)::[]
                                     ->
                                     let uu____38675 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____38675
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____38684)::(uu____38685,(arg,uu____38687))::[]
                                     ->
                                     let uu____38792 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____38792
                                 | (uu____38801,(p,uu____38803))::(uu____38804,
                                                                   (q,uu____38806))::[]
                                     ->
                                     let uu____38914 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____38914
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____38923 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____38945 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____38945
                                  then
                                    let uu____38952 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____38952 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____39034)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____39094)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____39154 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____39176 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____39176
                                     then
                                       match args with
                                       | (t,uu____39188)::[] ->
                                           let uu____39229 =
                                             let uu____39230 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____39230.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____39229 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____39245::[],body,uu____39247)
                                                ->
                                                let uu____39324 = simp_t body
                                                   in
                                                (match uu____39324 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____39334 -> tm1)
                                            | uu____39338 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____39340))::(t,uu____39342)::[]
                                           ->
                                           let uu____39410 =
                                             let uu____39411 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____39411.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____39410 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____39426::[],body,uu____39428)
                                                ->
                                                let uu____39505 = simp_t body
                                                   in
                                                (match uu____39505 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____39517 -> tm1)
                                            | uu____39521 -> tm1)
                                       | uu____39522 -> tm1
                                     else
                                       (let uu____39539 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____39539
                                        then
                                          match args with
                                          | (t,uu____39551)::[] ->
                                              let uu____39592 =
                                                let uu____39593 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____39593.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____39592 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____39608::[],body,uu____39610)
                                                   ->
                                                   let uu____39687 =
                                                     simp_t body  in
                                                   (match uu____39687 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____39697 -> tm1)
                                               | uu____39701 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____39703))::(t,uu____39705)::[]
                                              ->
                                              let uu____39773 =
                                                let uu____39774 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____39774.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____39773 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____39789::[],body,uu____39791)
                                                   ->
                                                   let uu____39868 =
                                                     simp_t body  in
                                                   (match uu____39868 with
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
                                                    | uu____39880 -> tm1)
                                               | uu____39884 -> tm1)
                                          | uu____39885 -> tm1
                                        else
                                          (let uu____39902 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____39902
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____39913;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____39914;_},uu____39915)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____39957;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____39958;_},uu____39959)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____40001 -> tm1
                                           else
                                             (let uu____40018 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____40018
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____40068 =
                                                    let uu____40069 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____40069.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____40068 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____40103 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     (Prims.parse_int "1")
                                                 then
                                                   let t =
                                                     let uu____40133 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____40133
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____40200 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____40200
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____40214 =
                                                         let uu____40215 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____40215.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____40214 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____40230 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____40255 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____40255
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____40280
                                                                  =
                                                                  let uu____40281
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____40281.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____40280
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____40299)
                                                                    -> hd1
                                                                | uu____40340
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____40348
                                                                =
                                                                let uu____40363
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____40363]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____40348)
                                                       | uu____40416 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____40421 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____40421 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____40461 ->
                                                     let uu____40474 =
                                                       let uu____40489 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____40489 cfg env
                                                        in
                                                     uu____40474 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____40495;
                         FStar_Syntax_Syntax.vars = uu____40496;_},args)
                      ->
                      let uu____40541 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____40541
                      then
                        let uu____40548 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____40548 with
                         | (FStar_Pervasives_Native.Some (true ),uu____40630)::
                             (uu____40631,(arg,uu____40633))::[] ->
                             maybe_auto_squash arg
                         | (uu____40738,(arg,uu____40740))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____40741)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____40846)::uu____40847::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____40941::(FStar_Pervasives_Native.Some (false
                                         ),uu____40942)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____41036 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____41058 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____41058
                         then
                           let uu____41065 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____41065 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____41147)::uu____41148::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____41242::(FStar_Pervasives_Native.Some (true
                                           ),uu____41243)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____41337)::(uu____41338,(arg,uu____41340))::[]
                               -> maybe_auto_squash arg
                           | (uu____41445,(arg,uu____41447))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____41448)::[]
                               -> maybe_auto_squash arg
                           | uu____41553 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____41575 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____41575
                            then
                              let uu____41582 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____41582 with
                              | uu____41664::(FStar_Pervasives_Native.Some
                                              (true ),uu____41665)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____41759)::uu____41760::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____41854)::(uu____41855,(arg,uu____41857))::[]
                                  -> maybe_auto_squash arg
                              | (uu____41962,(p,uu____41964))::(uu____41965,
                                                                (q,uu____41967))::[]
                                  ->
                                  let uu____42075 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____42075
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____42084 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____42106 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____42106
                               then
                                 let uu____42113 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____42113 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____42195)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____42196)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____42298)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____42299)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____42401)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____42402)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____42504)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____42505)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____42607,(arg,uu____42609))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____42610)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____42715)::(uu____42716,(arg,uu____42718))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____42823,(arg,uu____42825))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____42826)::[]
                                     ->
                                     let uu____42931 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____42931
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____42940)::(uu____42941,(arg,uu____42943))::[]
                                     ->
                                     let uu____43048 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____43048
                                 | (uu____43057,(p,uu____43059))::(uu____43060,
                                                                   (q,uu____43062))::[]
                                     ->
                                     let uu____43170 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____43170
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____43179 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____43201 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____43201
                                  then
                                    let uu____43208 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____43208 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____43290)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____43350)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____43410 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____43432 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____43432
                                     then
                                       match args with
                                       | (t,uu____43444)::[] ->
                                           let uu____43485 =
                                             let uu____43486 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____43486.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____43485 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____43501::[],body,uu____43503)
                                                ->
                                                let uu____43580 = simp_t body
                                                   in
                                                (match uu____43580 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____43590 -> tm1)
                                            | uu____43594 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____43596))::(t,uu____43598)::[]
                                           ->
                                           let uu____43666 =
                                             let uu____43667 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____43667.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____43666 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____43682::[],body,uu____43684)
                                                ->
                                                let uu____43761 = simp_t body
                                                   in
                                                (match uu____43761 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____43773 -> tm1)
                                            | uu____43777 -> tm1)
                                       | uu____43778 -> tm1
                                     else
                                       (let uu____43795 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____43795
                                        then
                                          match args with
                                          | (t,uu____43807)::[] ->
                                              let uu____43848 =
                                                let uu____43849 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____43849.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____43848 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____43864::[],body,uu____43866)
                                                   ->
                                                   let uu____43943 =
                                                     simp_t body  in
                                                   (match uu____43943 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____43953 -> tm1)
                                               | uu____43957 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____43959))::(t,uu____43961)::[]
                                              ->
                                              let uu____44029 =
                                                let uu____44030 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____44030.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____44029 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____44045::[],body,uu____44047)
                                                   ->
                                                   let uu____44124 =
                                                     simp_t body  in
                                                   (match uu____44124 with
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
                                                    | uu____44136 -> tm1)
                                               | uu____44140 -> tm1)
                                          | uu____44141 -> tm1
                                        else
                                          (let uu____44158 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____44158
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____44169;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____44170;_},uu____44171)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____44213;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____44214;_},uu____44215)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____44257 -> tm1
                                           else
                                             (let uu____44274 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____44274
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____44324 =
                                                    let uu____44325 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____44325.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____44324 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____44359 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     (Prims.parse_int "1")
                                                 then
                                                   let t =
                                                     let uu____44389 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____44389
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____44452 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____44452
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____44466 =
                                                         let uu____44467 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____44467.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____44466 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____44482 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____44507 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____44507
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____44532
                                                                  =
                                                                  let uu____44533
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____44533.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____44532
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____44551)
                                                                    -> hd1
                                                                | uu____44592
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____44600
                                                                =
                                                                let uu____44615
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____44615]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____44600)
                                                       | uu____44668 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____44673 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____44673 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____44713 ->
                                                     let uu____44726 =
                                                       let uu____44741 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____44741 cfg env
                                                        in
                                                     uu____44726 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____44770 = simp_t t  in
                      (match uu____44770 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____44783 ->
                      let uu____44821 = is_const_match tm1  in
                      (match uu____44821 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____44834 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____44887  ->
               (let uu____44889 = FStar_Syntax_Print.tag_of_term t  in
                let uu____44891 = FStar_Syntax_Print.term_to_string t  in
                let uu____44893 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____44901 =
                  let uu____44903 =
                    let uu____44906 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____44906
                     in
                  stack_to_string uu____44903  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____44889 uu____44891 uu____44893 uu____44901);
               (let uu____44931 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____44931
                then
                  let uu____44935 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____44935 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____44957 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____44959 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____44961 =
                          let uu____44963 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____44963
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____44957
                          uu____44959 uu____44961);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____44999 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack with
                | (Arg uu____45015)::uu____45016 -> true
                | uu____45026 -> false)
              in
           if uu____44999
           then
             let uu____45033 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____45033 (norm cfg env stack)
           else
             (let t1 = maybe_simplify cfg env stack t  in
              match stack with
              | [] -> t1
              | (Debug (tm,time_then))::stack1 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now ()  in
                      let uu____45095 =
                        let uu____45097 =
                          let uu____45099 =
                            FStar_Util.time_diff time_then time_now  in
                          FStar_Pervasives_Native.snd uu____45099  in
                        FStar_Util.string_of_int uu____45097  in
                      let uu____45106 = FStar_Syntax_Print.term_to_string tm
                         in
                      let uu____45108 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print3
                        "Normalized term (%s ms) %s\n\tto term %s\n"
                        uu____45095 uu____45106 uu____45108)
                   else ();
                   rebuild cfg env stack1 t1)
              | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
              | (Meta (uu____45152,m,r))::stack1 ->
                  let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
                  rebuild cfg env stack1 t2
              | (MemoLazy r)::stack1 ->
                  (set_memo cfg r (env, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu____45205  ->
                        let uu____45206 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 "\tSet memo %s\n" uu____45206);
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
                  let uu____45332 =
                    let uu___2745_45341 = FStar_Syntax_Util.abs bs1 t1 lopt1
                       in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___2745_45341.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___2745_45341.FStar_Syntax_Syntax.vars)
                    }  in
                  rebuild cfg env stack1 uu____45332
              | (Arg (Univ uu____45352,uu____45353,uu____45354))::uu____45355
                  -> failwith "Impossible"
              | (Arg (Dummy ,uu____45363,uu____45364))::uu____45365 ->
                  failwith "Impossible"
              | (UnivArgs (us,r))::stack1 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                  rebuild cfg env stack1 t2
              | (Arg
                  (Clos (env_arg,tm,uu____45393,uu____45394),aq,r))::stack1
                  when
                  let uu____45462 = head_of t1  in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____45462 ->
                  let t2 =
                    let uu____45482 =
                      let uu____45487 =
                        let uu____45488 = closure_as_term cfg env_arg tm  in
                        (uu____45488, aq)  in
                      FStar_Syntax_Syntax.extend_app t1 uu____45487  in
                    uu____45482 FStar_Pervasives_Native.None r  in
                  rebuild cfg env stack1 t2
              | (Arg (Clos (env_arg,tm,m,uu____45510),aq,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____45581  ->
                        let uu____45582 =
                          FStar_Syntax_Print.term_to_string tm  in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____45582);
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
                     (let uu____45634 = FStar_ST.op_Bang m  in
                      match uu____45634 with
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
                      | FStar_Pervasives_Native.Some (uu____45770,a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq)
                              FStar_Pervasives_Native.None r
                             in
                          rebuild cfg env_arg stack1 t2))
              | (App (env1,head1,aq,r))::stack' when should_reify cfg stack
                  ->
                  let t0 = t1  in
                  let fallback msg uu____45870 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____45875  ->
                         let uu____45876 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____45876);
                    (let t2 =
                       FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env1 stack' t2)
                     in
                  let uu____45898 =
                    let uu____45899 = FStar_Syntax_Subst.compress t1  in
                    uu____45899.FStar_Syntax_Syntax.n  in
                  (match uu____45898 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env1 stack t2 m
                         ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc,mtgt,ty))
                       ->
                       let lifted =
                         let uu____46003 = closure_as_term cfg env1 ty  in
                         reify_lift cfg t2 msrc mtgt uu____46003  in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____46015  ->
                             let uu____46016 =
                               FStar_Syntax_Print.term_to_string lifted  in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____46016);
                        (let uu____46019 = FStar_List.tl stack  in
                         norm cfg env1 uu____46019 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu____46020);
                          FStar_Syntax_Syntax.pos = uu____46021;
                          FStar_Syntax_Syntax.vars = uu____46022;_},(e,uu____46024)::[])
                       -> norm cfg env1 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____46095 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____46120 = FStar_Syntax_Util.head_and_args t1
                          in
                       (match uu____46120 with
                        | (hd1,args) ->
                            let uu____46191 =
                              let uu____46192 =
                                FStar_Syntax_Util.un_uinst hd1  in
                              uu____46192.FStar_Syntax_Syntax.n  in
                            (match uu____46191 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____46211 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv
                                    in
                                 (match uu____46211 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____46230;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____46231;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____46232;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n1;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____46234;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____46235;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____46236;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____46237;_}
                                      when (FStar_List.length args) = n1 ->
                                      norm cfg env1 stack' t1
                                  | uu____46303 -> fallback " (3)" ())
                             | uu____46319 -> fallback " (4)" ()))
                   | uu____46321 -> fallback " (2)" ())
              | (App (env1,head1,aq,r))::stack1 ->
                  let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack1 t2
              | (Match (env',branches,cfg1,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____46437  ->
                        let uu____46438 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____46438);
                   (let scrutinee_env = env  in
                    let env1 = env'  in
                    let scrutinee = t1  in
                    let norm_and_rebuild_match uu____46461 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____46466  ->
                           let uu____46467 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           let uu____46469 =
                             let uu____46471 =
                               FStar_All.pipe_right branches
                                 (FStar_List.map
                                    (fun uu____46517  ->
                                       match uu____46517 with
                                       | (p,uu____46536,uu____46537) ->
                                           FStar_Syntax_Print.pat_to_string p))
                                in
                             FStar_All.pipe_right uu____46471
                               (FStar_String.concat "\n\t")
                              in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu____46467 uu____46469);
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
                                (fun uu___17_46645  ->
                                   match uu___17_46645 with
                                   | FStar_TypeChecker_Env.InliningDelta  ->
                                       true
                                   | FStar_TypeChecker_Env.Eager_unfolding_only
                                       uu____46648 -> true
                                   | uu____46651 -> false))
                            in
                         let steps =
                           let uu___2914_46706 =
                             cfg1.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___2914_46706.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___2914_46706.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta = false;
                             FStar_TypeChecker_Cfg.weak =
                               (uu___2914_46706.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___2914_46706.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___2914_46706.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___2914_46706.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_only =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___2914_46706.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_tac = false;
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___2914_46706.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___2914_46706.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___2914_46706.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___2914_46706.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___2914_46706.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___2914_46706.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___2914_46706.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___2914_46706.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___2914_46706.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___2914_46706.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___2914_46706.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___2914_46706.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___2914_46706.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___2914_46706.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         let uu___2917_46773 = cfg1  in
                         {
                           FStar_TypeChecker_Cfg.steps = steps;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___2917_46773.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___2917_46773.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = new_delta;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___2917_46773.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong = true;
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___2917_46773.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets =
                             (uu___2917_46773.FStar_TypeChecker_Cfg.normalize_pure_lets);
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___2917_46773.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let norm_or_whnf env2 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env2 t2
                         else norm cfg_exclude_zeta env2 [] t2  in
                       let rec norm_pat env2 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu____46943 ->
                             (p, env2)
                         | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                             let uu____46989 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____47093  ->
                                       fun uu____47094  ->
                                         match (uu____47093, uu____47094)
                                         with
                                         | ((pats1,env3),(p1,b)) ->
                                             let uu____47271 =
                                               norm_pat env3 p1  in
                                             (match uu____47271 with
                                              | (p2,env4) ->
                                                  (((p2, b) :: pats1), env4)))
                                    ([], env2))
                                in
                             (match uu____46989 with
                              | (pats1,env3) ->
                                  ((let uu___2945_47480 = p  in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___2945_47480.FStar_Syntax_Syntax.p)
                                    }), env3))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___2949_47528 = x  in
                               let uu____47539 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2949_47528.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2949_47528.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____47539
                               }  in
                             ((let uu___2952_47564 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___2952_47564.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___2956_47593 = x  in
                               let uu____47604 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2956_47593.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2956_47593.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____47604
                               }  in
                             ((let uu___2959_47629 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___2959_47629.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                             let x1 =
                               let uu___2965_47676 = x  in
                               let uu____47687 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2965_47676.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2965_47676.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____47687
                               }  in
                             let t3 = norm_or_whnf env2 t2  in
                             ((let uu___2969_47721 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___2969_47721.FStar_Syntax_Syntax.p)
                               }), env2)
                          in
                       let branches1 =
                         match env1 with
                         | [] when whnf -> branches
                         | uu____47799 ->
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun branch1  ->
                                     let uu____47840 =
                                       FStar_Syntax_Subst.open_branch branch1
                                        in
                                     match uu____47840 with
                                     | (p,wopt,e) ->
                                         let uu____47882 = norm_pat env1 p
                                            in
                                         (match uu____47882 with
                                          | (p1,env2) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu____47970 =
                                                      norm_or_whnf env2 w  in
                                                    FStar_Pervasives_Native.Some
                                                      uu____47970
                                                 in
                                              let e1 = norm_or_whnf env2 e
                                                 in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1))))
                          in
                       let scrutinee1 =
                         let uu____48026 =
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
                         if uu____48026
                         then
                           norm
                             (let uu___2988_48037 = cfg1  in
                              {
                                FStar_TypeChecker_Cfg.steps =
                                  (let uu___2990_48110 =
                                     cfg1.FStar_TypeChecker_Cfg.steps  in
                                   {
                                     FStar_TypeChecker_Cfg.beta =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.beta);
                                     FStar_TypeChecker_Cfg.iota =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.iota);
                                     FStar_TypeChecker_Cfg.zeta =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.zeta);
                                     FStar_TypeChecker_Cfg.weak =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.weak);
                                     FStar_TypeChecker_Cfg.hnf =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.hnf);
                                     FStar_TypeChecker_Cfg.primops =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.primops);
                                     FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                       =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                     FStar_TypeChecker_Cfg.unfold_until =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.unfold_until);
                                     FStar_TypeChecker_Cfg.unfold_only =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.unfold_only);
                                     FStar_TypeChecker_Cfg.unfold_fully =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.unfold_fully);
                                     FStar_TypeChecker_Cfg.unfold_attr =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.unfold_attr);
                                     FStar_TypeChecker_Cfg.unfold_tac =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.unfold_tac);
                                     FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                       =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                     FStar_TypeChecker_Cfg.simplify =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.simplify);
                                     FStar_TypeChecker_Cfg.erase_universes =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.erase_universes);
                                     FStar_TypeChecker_Cfg.allow_unbound_universes
                                       =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                     FStar_TypeChecker_Cfg.reify_ =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.reify_);
                                     FStar_TypeChecker_Cfg.compress_uvars =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.compress_uvars);
                                     FStar_TypeChecker_Cfg.no_full_norm =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.no_full_norm);
                                     FStar_TypeChecker_Cfg.check_no_uvars =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.check_no_uvars);
                                     FStar_TypeChecker_Cfg.unmeta =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.unmeta);
                                     FStar_TypeChecker_Cfg.unascribe =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.unascribe);
                                     FStar_TypeChecker_Cfg.in_full_norm_request
                                       =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.in_full_norm_request);
                                     FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                       = false;
                                     FStar_TypeChecker_Cfg.nbe_step =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.nbe_step);
                                     FStar_TypeChecker_Cfg.for_extraction =
                                       (uu___2990_48110.FStar_TypeChecker_Cfg.for_extraction)
                                   });
                                FStar_TypeChecker_Cfg.tcenv =
                                  (uu___2988_48037.FStar_TypeChecker_Cfg.tcenv);
                                FStar_TypeChecker_Cfg.debug =
                                  (uu___2988_48037.FStar_TypeChecker_Cfg.debug);
                                FStar_TypeChecker_Cfg.delta_level =
                                  (uu___2988_48037.FStar_TypeChecker_Cfg.delta_level);
                                FStar_TypeChecker_Cfg.primitive_steps =
                                  (uu___2988_48037.FStar_TypeChecker_Cfg.primitive_steps);
                                FStar_TypeChecker_Cfg.strong =
                                  (uu___2988_48037.FStar_TypeChecker_Cfg.strong);
                                FStar_TypeChecker_Cfg.memoize_lazy =
                                  (uu___2988_48037.FStar_TypeChecker_Cfg.memoize_lazy);
                                FStar_TypeChecker_Cfg.normalize_pure_lets =
                                  (uu___2988_48037.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                FStar_TypeChecker_Cfg.reifying =
                                  (uu___2988_48037.FStar_TypeChecker_Cfg.reifying)
                              }) scrutinee_env [] scrutinee
                         else scrutinee  in
                       let uu____48166 =
                         mk
                           (FStar_Syntax_Syntax.Tm_match
                              (scrutinee1, branches1)) r
                          in
                       rebuild cfg1 env1 stack1 uu____48166)
                       in
                    let rec is_cons head1 =
                      let uu____48223 =
                        let uu____48224 = FStar_Syntax_Subst.compress head1
                           in
                        uu____48224.FStar_Syntax_Syntax.n  in
                      match uu____48223 with
                      | FStar_Syntax_Syntax.Tm_uinst (h,uu____48237) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____48250 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____48252;
                            FStar_Syntax_Syntax.fv_delta = uu____48253;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor );_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____48255;
                            FStar_Syntax_Syntax.fv_delta = uu____48256;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____48257);_}
                          -> true
                      | uu____48271 -> false  in
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
                      let uu____48586 =
                        FStar_Syntax_Util.head_and_args scrutinee2  in
                      match uu____48586 with
                      | (head1,args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu____48807 ->
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
                                | uu____48903 ->
                                    let uu____48904 =
                                      let uu____48906 = is_cons head1  in
                                      Prims.op_Negation uu____48906  in
                                    FStar_Util.Inr uu____48904)
                           | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                               let uu____48956 =
                                 let uu____48957 =
                                   FStar_Syntax_Util.un_uinst head1  in
                                 uu____48957.FStar_Syntax_Syntax.n  in
                               (match uu____48956 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____49005 ->
                                    let uu____49006 =
                                      let uu____49008 = is_cons head1  in
                                      Prims.op_Negation uu____49008  in
                                    FStar_Util.Inr uu____49006))
                    
                    and matches_args out a p =
                      match (a, p) with
                      | ([],[]) -> FStar_Util.Inl out
                      | ((t2,uu____49147)::rest_a,(p1,uu____49150)::rest_p)
                          ->
                          let uu____49229 = matches_pat t2 p1  in
                          (match uu____49229 with
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu____49336 -> FStar_Util.Inr false
                     in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1,wopt,b)::rest ->
                          let uu____49544 = matches_pat scrutinee1 p1  in
                          (match uu____49544 with
                           | FStar_Util.Inr (false ) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true ) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu____49639  ->
                                     let uu____49640 =
                                       FStar_Syntax_Print.pat_to_string p1
                                        in
                                     let uu____49642 =
                                       let uu____49644 =
                                         FStar_List.map
                                           (fun uu____49665  ->
                                              match uu____49665 with
                                              | (uu____49680,t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s
                                          in
                                       FStar_All.pipe_right uu____49644
                                         (FStar_String.concat "; ")
                                        in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu____49640 uu____49642);
                                (let env0 = env1  in
                                 let env2 =
                                   FStar_List.fold_left
                                     (fun env2  ->
                                        fun uu____49743  ->
                                          match uu____49743 with
                                          | (bv,t2) ->
                                              let uu____49793 =
                                                let uu____49800 =
                                                  let uu____49803 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____49803
                                                   in
                                                let uu____49804 =
                                                  let uu____49805 =
                                                    let uu____49845 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2))
                                                       in
                                                    ([], t2, uu____49845,
                                                      false)
                                                     in
                                                  Clos uu____49805  in
                                                (uu____49800, uu____49804)
                                                 in
                                              uu____49793 :: env2) env1 s
                                    in
                                 let uu____49962 =
                                   guard_when_clause wopt b rest  in
                                 norm cfg1 env2 stack1 uu____49962)))
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
            (fun uu____50221  ->
               let uu____50222 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____50222);
          (let uu____50225 = is_nbe_request s  in
           if uu____50225
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____50235  ->
                   let uu____50236 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____50236);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____50242  ->
                   let uu____50243 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____50243);
              (let uu____50246 =
                 FStar_Util.record_time (fun uu____50261  -> nbe_eval c s t)
                  in
               match uu____50246 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____50282  ->
                         let uu____50283 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____50285 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____50283 uu____50285);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____50293  ->
                   let uu____50294 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____50294);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____50300  ->
                   let uu____50301 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____50301);
              (let uu____50304 =
                 FStar_Util.record_time (fun uu____50319  -> norm c [] [] t)
                  in
               match uu____50304 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____50346  ->
                         let uu____50347 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____50349 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____50347 uu____50349);
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
        let uu____50636 = FStar_TypeChecker_Cfg.config s e  in
        norm_comp uu____50636 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____50832 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____50832 [] u
  
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
        let uu____51126 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____51126  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____51145 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___3146_51176 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3146_51176.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3146_51176.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name
              cfg.FStar_TypeChecker_Cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____51208 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____51208
          then
            let ct1 =
              let uu____51226 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____51226 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____51250 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____51250
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3156_51257 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3156_51257.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3156_51257.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3156_51257.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev
                      cfg.FStar_TypeChecker_Cfg.tcenv c
                     in
                  let uu___3160_51283 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3160_51283.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3160_51283.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3160_51283.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3160_51283.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3163_51294 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3163_51294.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3163_51294.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____51305 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      let cfg =
        FStar_TypeChecker_Cfg.config
          [FStar_TypeChecker_Env.UnfoldUntil
             FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses;
          FStar_TypeChecker_Env.Unascribe;
          FStar_TypeChecker_Env.ForExtraction] env
         in
      let non_info t =
        let uu____51535 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____51535  in
      let uu____51550 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____51550
      then
        let uu____51561 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____51561 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____51587  ->
                 let uu____51588 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____51588)
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
          (fun uu___3179_51745  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___3178_51752 ->
            ((let uu____51758 =
                let uu____51764 =
                  let uu____51766 = FStar_Util.message_of_exn uu___3178_51752
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____51766
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____51764)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____51758);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          (fun uu___3189_51913  ->
             match () with
             | () ->
                 let uu____51918 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____51918 [] c) ()
        with
        | uu___3188_51997 ->
            ((let uu____52003 =
                let uu____52009 =
                  let uu____52011 = FStar_Util.message_of_exn uu___3188_51997
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____52011
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____52009)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____52003);
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
                   let uu____52260 =
                     let uu____52261 =
                       let uu____52277 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____52277)  in
                     FStar_Syntax_Syntax.Tm_refine uu____52261  in
                   mk uu____52260 t01.FStar_Syntax_Syntax.pos
               | uu____52299 -> t2)
          | uu____52300 -> t2  in
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
        let uu____53122 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____53122 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____53199 ->
                 let uu____53213 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____53213 with
                  | (actuals,uu____53238,uu____53239) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____53295 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____53295 with
                         | (binders,args) ->
                             let uu____53310 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____53310
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
      | uu____53469 ->
          let uu____53470 = FStar_Syntax_Util.head_and_args t  in
          (match uu____53470 with
           | (head1,args) ->
               let uu____53541 =
                 let uu____53542 = FStar_Syntax_Subst.compress head1  in
                 uu____53542.FStar_Syntax_Syntax.n  in
               (match uu____53541 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____53591 =
                      let uu____53615 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____53615  in
                    (match uu____53591 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____53698 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___3259_53718 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3259_53718.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3259_53718.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3259_53718.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3259_53718.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3259_53718.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3259_53718.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3259_53718.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3259_53718.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3259_53718.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___3259_53718.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3259_53718.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3259_53718.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3259_53718.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3259_53718.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3259_53718.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3259_53718.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3259_53718.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3259_53718.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3259_53718.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3259_53718.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3259_53718.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3259_53718.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3259_53718.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3259_53718.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3259_53718.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3259_53718.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3259_53718.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3259_53718.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3259_53718.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3259_53718.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3259_53718.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3259_53718.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3259_53718.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3259_53718.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3259_53718.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___3259_53718.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3259_53718.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3259_53718.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3259_53718.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3259_53718.FStar_TypeChecker_Env.nbe)
                                 }) t
                               in
                            match uu____53698 with
                            | (uu____53837,ty,uu____53839) ->
                                eta_expand_with_type env t ty))
                | uu____53864 ->
                    let uu____53865 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___3266_53885 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3266_53885.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3266_53885.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3266_53885.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3266_53885.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3266_53885.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3266_53885.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3266_53885.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3266_53885.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3266_53885.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___3266_53885.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3266_53885.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3266_53885.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3266_53885.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3266_53885.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3266_53885.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3266_53885.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3266_53885.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3266_53885.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3266_53885.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3266_53885.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3266_53885.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3266_53885.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3266_53885.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3266_53885.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3266_53885.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3266_53885.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3266_53885.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3266_53885.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3266_53885.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3266_53885.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3266_53885.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3266_53885.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3266_53885.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3266_53885.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3266_53885.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___3266_53885.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3266_53885.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3266_53885.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3266_53885.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3266_53885.FStar_TypeChecker_Env.nbe)
                         }) t
                       in
                    (match uu____53865 with
                     | (uu____54004,ty,uu____54006) ->
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
      let uu___3278_54181 = x  in
      let uu____54192 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3278_54181.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3278_54181.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____54192
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____54207 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____54243 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____54249 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____54255 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____54259 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____54270 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____54271 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____54272 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3304_54363 = rc  in
          let uu____54378 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____54399 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3304_54363.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____54378;
            FStar_Syntax_Syntax.residual_flags = uu____54399
          }  in
        let uu____54402 =
          let uu____54403 =
            let uu____54438 = elim_delayed_subst_binders bs  in
            let uu____54452 = elim_delayed_subst_term t2  in
            let uu____54463 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____54438, uu____54452, uu____54463)  in
          FStar_Syntax_Syntax.Tm_abs uu____54403  in
        mk1 uu____54402
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____54555 =
          let uu____54556 =
            let uu____54580 = elim_delayed_subst_binders bs  in
            let uu____54594 = elim_delayed_subst_comp c  in
            (uu____54580, uu____54594)  in
          FStar_Syntax_Syntax.Tm_arrow uu____54556  in
        mk1 uu____54555
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____54648 =
          let uu____54649 =
            let uu____54665 = elim_bv bv  in
            let uu____54676 = elim_delayed_subst_term phi  in
            (uu____54665, uu____54676)  in
          FStar_Syntax_Syntax.Tm_refine uu____54649  in
        mk1 uu____54648
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____54740 =
          let uu____54741 =
            let uu____54766 = elim_delayed_subst_term t2  in
            let uu____54777 = elim_delayed_subst_args args  in
            (uu____54766, uu____54777)  in
          FStar_Syntax_Syntax.Tm_app uu____54741  in
        mk1 uu____54740
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3326_54902 = p  in
              let uu____54903 =
                let uu____54904 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____54904  in
              {
                FStar_Syntax_Syntax.v = uu____54903;
                FStar_Syntax_Syntax.p =
                  (uu___3326_54902.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3330_54921 = p  in
              let uu____54922 =
                let uu____54923 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____54923  in
              {
                FStar_Syntax_Syntax.v = uu____54922;
                FStar_Syntax_Syntax.p =
                  (uu___3330_54921.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3336_54958 = p  in
              let uu____54959 =
                let uu____54960 =
                  let uu____54976 = elim_bv x  in
                  let uu____54987 = elim_delayed_subst_term t0  in
                  (uu____54976, uu____54987)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____54960  in
              {
                FStar_Syntax_Syntax.v = uu____54959;
                FStar_Syntax_Syntax.p =
                  (uu___3336_54958.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3342_55041 = p  in
              let uu____55042 =
                let uu____55043 =
                  let uu____55063 =
                    FStar_List.map
                      (fun uu____55095  ->
                         match uu____55095 with
                         | (x,b) ->
                             let uu____55115 = elim_pat x  in
                             (uu____55115, b)) pats
                     in
                  (fv, uu____55063)  in
                FStar_Syntax_Syntax.Pat_cons uu____55043  in
              {
                FStar_Syntax_Syntax.v = uu____55042;
                FStar_Syntax_Syntax.p =
                  (uu___3342_55041.FStar_Syntax_Syntax.p)
              }
          | uu____55142 -> p  in
        let elim_branch uu____55185 =
          match uu____55185 with
          | (pat,wopt,t3) ->
              let uu____55246 = elim_pat pat  in
              let uu____55252 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____55267 = elim_delayed_subst_term t3  in
              (uu____55246, uu____55252, uu____55267)
           in
        let uu____55291 =
          let uu____55292 =
            let uu____55330 = elim_delayed_subst_term t2  in
            let uu____55341 = FStar_List.map elim_branch branches  in
            (uu____55330, uu____55341)  in
          FStar_Syntax_Syntax.Tm_match uu____55292  in
        mk1 uu____55291
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____55584 =
          match uu____55584 with
          | (tc,topt) ->
              let uu____55667 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____55705 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____55705
                | FStar_Util.Inr c ->
                    let uu____55735 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____55735
                 in
              let uu____55752 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____55667, uu____55752)
           in
        let uu____55785 =
          let uu____55786 =
            let uu____55833 = elim_delayed_subst_term t2  in
            let uu____55844 = elim_ascription a  in
            (uu____55833, uu____55844, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____55786  in
        mk1 uu____55785
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3372_55982 = lb  in
          let uu____55997 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____56008 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3372_55982.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3372_55982.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____55997;
            FStar_Syntax_Syntax.lbeff =
              (uu___3372_55982.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____56008;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3372_55982.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3372_55982.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____56019 =
          let uu____56020 =
            let uu____56045 =
              let uu____56060 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____56060)  in
            let uu____56114 = elim_delayed_subst_term t2  in
            (uu____56045, uu____56114)  in
          FStar_Syntax_Syntax.Tm_let uu____56020  in
        mk1 uu____56019
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____56218 =
          let uu____56219 =
            let uu____56232 = elim_delayed_subst_term tm  in
            (uu____56232, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____56219  in
        mk1 uu____56218
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____56265 =
          let uu____56266 =
            let uu____56277 = elim_delayed_subst_term t2  in
            let uu____56288 = elim_delayed_subst_meta md  in
            (uu____56277, uu____56288)  in
          FStar_Syntax_Syntax.Tm_meta uu____56266  in
        mk1 uu____56265

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
      (fun uu___18_56301  ->
         match uu___18_56301 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____56309 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____56309
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
        let uu____56364 =
          let uu____56365 =
            let uu____56378 = elim_delayed_subst_term t  in
            (uu____56378, uopt)  in
          FStar_Syntax_Syntax.Total uu____56365  in
        mk1 uu____56364
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____56415 =
          let uu____56416 =
            let uu____56429 = elim_delayed_subst_term t  in
            (uu____56429, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____56416  in
        mk1 uu____56415
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3405_56465 = ct  in
          let uu____56476 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____56487 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____56502 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3405_56465.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3405_56465.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____56476;
            FStar_Syntax_Syntax.effect_args = uu____56487;
            FStar_Syntax_Syntax.flags = uu____56502
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___19_56505  ->
    match uu___19_56505 with
    | FStar_Syntax_Syntax.Meta_pattern (names1,args) ->
        let uu____56556 =
          let uu____56585 = FStar_List.map elim_delayed_subst_term names1  in
          let uu____56606 = FStar_List.map elim_delayed_subst_args args  in
          (uu____56585, uu____56606)  in
        FStar_Syntax_Syntax.Meta_pattern uu____56556
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____56697 =
          let uu____56712 = elim_delayed_subst_term t  in (m, uu____56712)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____56697
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____56764 =
          let uu____56785 = elim_delayed_subst_term t  in
          (m1, m2, uu____56785)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____56764
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
      (fun uu____56850  ->
         match uu____56850 with
         | (t,q) ->
             let uu____56885 = elim_delayed_subst_term t  in (uu____56885, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____56940  ->
         match uu____56940 with
         | (x,q) ->
             let uu____56979 =
               let uu___3431_56990 = x  in
               let uu____57001 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3431_56990.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3431_56990.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____57001
               }  in
             (uu____56979, q)) bs

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
            | (uu____57348,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____57419,FStar_Util.Inl t) ->
                let uu____57471 =
                  let uu____57478 =
                    let uu____57479 =
                      let uu____57503 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____57503)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____57479  in
                  FStar_Syntax_Syntax.mk uu____57478  in
                uu____57471 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____57533 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____57533 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____57614 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____57744 ->
                    let uu____57745 =
                      let uu____57762 =
                        let uu____57763 = FStar_Syntax_Subst.compress t4  in
                        uu____57763.FStar_Syntax_Syntax.n  in
                      (uu____57762, tc)  in
                    (match uu____57745 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____57821) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____57927) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____58031,FStar_Util.Inl uu____58032) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____58109 -> failwith "Impossible")
                 in
              (match uu____57614 with
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
          let uu____58446 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____58446 with
          | (univ_names1,binders1,tc) ->
              let uu____58576 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____58576)
  
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
          let uu____58780 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____58780 with
          | (univ_names1,binders1,tc) ->
              let uu____58910 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____58910)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____59137 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____59137 with
           | (univ_names1,binders1,typ1) ->
               let uu___3514_59209 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3514_59209.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3514_59209.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3514_59209.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3514_59209.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___3520_59268 = s  in
          let uu____59279 =
            let uu____59280 =
              let uu____59298 = FStar_List.map (elim_uvars env) sigs  in
              (uu____59298, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____59280  in
          {
            FStar_Syntax_Syntax.sigel = uu____59279;
            FStar_Syntax_Syntax.sigrng =
              (uu___3520_59268.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3520_59268.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3520_59268.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3520_59268.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____59373 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____59373 with
           | (univ_names1,uu____59416,typ1) ->
               let uu___3534_59456 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3534_59456.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3534_59456.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3534_59456.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3534_59456.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____59505 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____59505 with
           | (univ_names1,uu____59548,typ1) ->
               let uu___3545_59588 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3545_59588.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3545_59588.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3545_59588.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3545_59588.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____59700 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____59700 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____59750 =
                            let uu____59759 =
                              let uu____59768 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____59768  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____59759
                             in
                          elim_delayed_subst_term uu____59750  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___3561_59795 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3561_59795.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3561_59795.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3561_59795.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3561_59795.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___3564_59810 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___3564_59810.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3564_59810.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3564_59810.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3564_59810.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___3568_59842 = s  in
          let uu____59853 =
            let uu____59854 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____59854  in
          {
            FStar_Syntax_Syntax.sigel = uu____59853;
            FStar_Syntax_Syntax.sigrng =
              (uu___3568_59842.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3568_59842.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3568_59842.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3568_59842.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____59882 = elim_uvars_aux_t env us [] t  in
          (match uu____59882 with
           | (us1,uu____59925,t1) ->
               let uu___3579_59965 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3579_59965.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3579_59965.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3579_59965.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3579_59965.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____59984 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____60032 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____60032 with
           | (univs1,binders,signature) ->
               let uu____60104 =
                 let uu____60109 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____60109 with
                 | (univs_opening,univs2) ->
                     let uu____60138 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____60138)
                  in
               (match uu____60104 with
                | (univs_opening,univs_closing) ->
                    let uu____60146 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____60152 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____60153 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____60152, uu____60153)  in
                    (match uu____60146 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____60201 =
                           match uu____60201 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____60243 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____60243 with
                                | (us1,t1) ->
                                    let uu____60270 =
                                      let uu____60279 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____60284 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____60279, uu____60284)  in
                                    (match uu____60270 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____60311 =
                                           let uu____60320 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____60325 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____60320, uu____60325)  in
                                         (match uu____60311 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____60361 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____60361
                                                 in
                                              let uu____60370 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____60370 with
                                               | (uu____60417,uu____60418,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____60467 =
                                                       let uu____60476 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____60476
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____60467
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____60509 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____60509 with
                           | (uu____60541,uu____60542,t1) -> t1  in
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
                             | uu____60739 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____60805 =
                               let uu____60806 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____60806.FStar_Syntax_Syntax.n  in
                             match uu____60805 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____60945 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____61008 =
                               let uu____61009 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____61009.FStar_Syntax_Syntax.n  in
                             match uu____61008 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____61053) ->
                                 let uu____61110 = destruct_action_body body
                                    in
                                 (match uu____61110 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____61209 ->
                                 let uu____61210 = destruct_action_body t  in
                                 (match uu____61210 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____61320 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____61320 with
                           | (action_univs,t) ->
                               let uu____61357 = destruct_action_typ_templ t
                                  in
                               (match uu____61357 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___3665_61473 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3665_61473.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3665_61473.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___3668_61535 = ed  in
                           let uu____61576 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____61577 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____61578 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____61579 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____61580 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____61581 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____61582 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____61583 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____61584 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____61585 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____61586 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____61595 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____61596 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____61597 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___3668_61535.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___3668_61535.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____61576;
                             FStar_Syntax_Syntax.bind_wp = uu____61577;
                             FStar_Syntax_Syntax.if_then_else = uu____61578;
                             FStar_Syntax_Syntax.ite_wp = uu____61579;
                             FStar_Syntax_Syntax.stronger = uu____61580;
                             FStar_Syntax_Syntax.close_wp = uu____61581;
                             FStar_Syntax_Syntax.assert_p = uu____61582;
                             FStar_Syntax_Syntax.assume_p = uu____61583;
                             FStar_Syntax_Syntax.null_wp = uu____61584;
                             FStar_Syntax_Syntax.trivial = uu____61585;
                             FStar_Syntax_Syntax.repr = uu____61586;
                             FStar_Syntax_Syntax.return_repr = uu____61595;
                             FStar_Syntax_Syntax.bind_repr = uu____61596;
                             FStar_Syntax_Syntax.actions = uu____61597;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3668_61535.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___3671_61630 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3671_61630.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3671_61630.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3671_61630.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3671_61630.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___20_61677 =
            match uu___20_61677 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____61736 = elim_uvars_aux_t env us [] t  in
                (match uu____61736 with
                 | (us1,uu____61786,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___3686_61859 = sub_eff  in
            let uu____61876 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____61879 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___3686_61859.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3686_61859.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____61876;
              FStar_Syntax_Syntax.lift = uu____61879
            }  in
          let uu___3689_61882 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___3689_61882.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3689_61882.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3689_61882.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3689_61882.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____61918 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____61918 with
           | (univ_names1,binders1,comp1) ->
               let uu___3702_61990 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3702_61990.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3702_61990.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3702_61990.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3702_61990.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____62011 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____62012 -> s
  
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
        let uu____62319 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____62319 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____62369 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____62369 with
             | (uu____62384,head_def) ->
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
      let uu____62418 = FStar_Syntax_Util.head_and_args t  in
      match uu____62418 with
      | (head1,args) ->
          let uu____62491 =
            let uu____62492 = FStar_Syntax_Subst.compress head1  in
            uu____62492.FStar_Syntax_Syntax.n  in
          (match uu____62491 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____62514;
                  FStar_Syntax_Syntax.vars = uu____62515;_},us)
               -> aux fv us args
           | uu____62532 -> FStar_Pervasives_Native.None)
  