open Prims
let cases :
  'Auu____59225 'Auu____59226 .
    ('Auu____59225 -> 'Auu____59226) ->
      'Auu____59226 ->
        'Auu____59225 FStar_Pervasives_Native.option -> 'Auu____59226
  =
  fun f  ->
    fun d  ->
      fun uu___585_59246  ->
        match uu___585_59246 with
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
    match projectee with | Clos _0 -> true | uu____59344 -> false
  
let (__proj__Clos__item___0 :
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
      Prims.list * FStar_Syntax_Syntax.term * ((FStar_Syntax_Syntax.binder
      FStar_Pervasives_Native.option * closure) Prims.list *
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool))
  = fun projectee  -> match projectee with | Clos _0 -> _0 
let (uu___is_Univ : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____59456 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____59474 -> false
  
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
    match projectee with | Arg _0 -> true | uu____59643 -> false
  
let (__proj__Arg__item___0 :
  stack_elt -> (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)) =
  fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____59686 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range))
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____59729 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo) =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____59774 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env * branches * FStar_TypeChecker_Cfg.cfg * FStar_Range.range))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____59829 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * env *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
      FStar_Range.range))
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____59892 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Range.range))
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____59941 -> false
  
let (__proj__Meta__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.metadata * FStar_Range.range)) =
  fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____59986 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding *
      FStar_Range.range))
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____60029 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> FStar_TypeChecker_Cfg.cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____60052 -> false
  
let (__proj__Debug__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.term * FStar_Util.time)) =
  fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____60081 = FStar_Syntax_Util.head_and_args' t  in
    match uu____60081 with | (hd1,uu____60097) -> hd1
  
let mk :
  'Auu____60125 .
    'Auu____60125 ->
      FStar_Range.range -> 'Auu____60125 FStar_Syntax_Syntax.syntax
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
          let uu____60168 = FStar_ST.op_Bang r  in
          match uu____60168 with
          | FStar_Pervasives_Native.Some uu____60194 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____60249 =
      FStar_List.map
        (fun uu____60265  ->
           match uu____60265 with
           | (bopt,c) ->
               let uu____60279 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____60284 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____60279 uu____60284) env
       in
    FStar_All.pipe_right uu____60249 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___586_60292  ->
    match uu___586_60292 with
    | Clos (env,t,uu____60296,uu____60297) ->
        let uu____60344 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____60354 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____60344 uu____60354
    | Univ uu____60357 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___587_60366  ->
    match uu___587_60366 with
    | Arg (c,uu____60369,uu____60370) ->
        let uu____60371 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____60371
    | MemoLazy uu____60374 -> "MemoLazy"
    | Abs (uu____60382,bs,uu____60384,uu____60385,uu____60386) ->
        let uu____60391 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____60391
    | UnivArgs uu____60402 -> "UnivArgs"
    | Match uu____60410 -> "Match"
    | App (uu____60420,t,uu____60422,uu____60423) ->
        let uu____60424 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____60424
    | Meta (uu____60427,m,uu____60429) -> "Meta"
    | Let uu____60431 -> "Let"
    | Cfg uu____60441 -> "Cfg"
    | Debug (t,uu____60444) ->
        let uu____60445 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____60445
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____60459 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____60459 (FStar_String.concat "; ")
  
let is_empty : 'Auu____60474 . 'Auu____60474 Prims.list -> Prims.bool =
  fun uu___588_60482  ->
    match uu___588_60482 with | [] -> true | uu____60486 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        (fun uu___700_60519  ->
           match () with
           | () ->
               let uu____60520 =
                 FStar_List.nth env x.FStar_Syntax_Syntax.index  in
               FStar_Pervasives_Native.snd uu____60520) ()
      with
      | uu___699_60537 ->
          let uu____60538 =
            let uu____60540 = FStar_Syntax_Print.db_to_string x  in
            let uu____60542 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____60540
              uu____60542
             in
          failwith uu____60538
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____60553 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____60553
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____60560 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____60560
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____60567 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____60567
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
          let uu____60605 =
            FStar_List.fold_left
              (fun uu____60631  ->
                 fun u1  ->
                   match uu____60631 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____60656 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____60656 with
                        | (k_u,n1) ->
                            let uu____60674 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____60674
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____60605 with
          | (uu____60695,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 (fun uu___734_60721  ->
                    match () with
                    | () ->
                        let uu____60724 =
                          let uu____60725 = FStar_List.nth env x  in
                          FStar_Pervasives_Native.snd uu____60725  in
                        (match uu____60724 with
                         | Univ u3 ->
                             ((let uu____60744 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      cfg.FStar_TypeChecker_Cfg.tcenv)
                                   (FStar_Options.Other "univ_norm")
                                  in
                               if uu____60744
                               then
                                 let uu____60749 =
                                   FStar_Syntax_Print.univ_to_string u3  in
                                 FStar_Util.print1
                                   "Univ (in norm_universe): %s\n"
                                   uu____60749
                               else ());
                              aux u3)
                         | Dummy  -> [u2]
                         | uu____60754 ->
                             let uu____60755 =
                               let uu____60757 = FStar_Util.string_of_int x
                                  in
                               FStar_Util.format1
                                 "Impossible: universe variable u@%s bound to a term"
                                 uu____60757
                                in
                             failwith uu____60755)) ()
               with
               | uu____60767 ->
                   if
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else
                     (let uu____60773 =
                        let uu____60775 = FStar_Util.string_of_int x  in
                        FStar_String.op_Hat "Universe variable not found: u@"
                          uu____60775
                         in
                      failwith uu____60773))
          | FStar_Syntax_Syntax.U_unif uu____60780 when
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____60789 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____60798 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____60805 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____60805 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____60822 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____60822 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____60833 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____60843 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____60843 with
                                  | (uu____60850,m) -> n1 <= m))
                           in
                        if uu____60833 then rest1 else us1
                    | uu____60859 -> us1)
               | uu____60865 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____60869 = aux u3  in
              FStar_List.map
                (fun _60872  -> FStar_Syntax_Syntax.U_succ _60872)
                uu____60869
           in
        if
          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____60876 = aux u  in
           match uu____60876 with
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
            (fun uu____61045  ->
               let uu____61046 = FStar_Syntax_Print.tag_of_term t  in
               let uu____61048 = env_to_string env  in
               let uu____61050 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____61046 uu____61048 uu____61050);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____61063 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____61066 ->
                    let uu____61089 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____61089
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____61090 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____61091 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____61092 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____61093 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____61118 ->
                           let uu____61131 =
                             let uu____61133 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____61135 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____61133 uu____61135
                              in
                           failwith uu____61131
                       | uu____61140 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___589_61176  ->
                                         match uu___589_61176 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____61183 =
                                               let uu____61190 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____61190)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____61183
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___828_61202 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___828_61202.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___828_61202.FStar_Syntax_Syntax.sort)
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
                                              | uu____61208 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____61211 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___837_61216 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___837_61216.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___837_61216.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____61237 =
                        let uu____61238 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____61238  in
                      mk uu____61237 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____61246 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____61246  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____61248 = lookup_bvar env x  in
                    (match uu____61248 with
                     | Univ uu____61251 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___853_61256 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___853_61256.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___853_61256.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____61262,uu____61263) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____61354  ->
                              fun stack1  ->
                                match uu____61354 with
                                | (a,aq) ->
                                    let uu____61366 =
                                      let uu____61367 =
                                        let uu____61374 =
                                          let uu____61375 =
                                            let uu____61407 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____61407, false)  in
                                          Clos uu____61375  in
                                        (uu____61374, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____61367  in
                                    uu____61366 :: stack1) args)
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
                    let uu____61575 = close_binders cfg env bs  in
                    (match uu____61575 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,uu____61625) when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    ->
                    inline_closure_env cfg env stack
                      x.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____61636 =
                      let uu____61649 =
                        let uu____61658 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____61658]  in
                      close_binders cfg env uu____61649  in
                    (match uu____61636 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____61703 =
                             let uu____61704 =
                               let uu____61711 =
                                 let uu____61712 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____61712
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____61711, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____61704  in
                           mk uu____61703 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____61811 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____61811
                      | FStar_Util.Inr c ->
                          let uu____61825 = close_comp cfg env c  in
                          FStar_Util.Inr uu____61825
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____61844 =
                        let uu____61845 =
                          let uu____61872 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____61872, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____61845  in
                      mk uu____61844 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____61918 =
                            let uu____61919 =
                              let uu____61926 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____61926, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____61919  in
                          mk uu____61918 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____61981  -> dummy :: env1) env
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
                    let uu____62002 =
                      let uu____62013 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____62013
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____62035 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___945_62051 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___945_62051.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___945_62051.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____62035))
                       in
                    (match uu____62002 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___950_62069 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___950_62069.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___950_62069.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___950_62069.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___950_62069.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____62086,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____62152  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____62169 =
                          FStar_Syntax_Syntax.is_top_level lbs  in
                        if uu____62169
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____62184  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____62208 =
                          FStar_Syntax_Syntax.is_top_level lbs  in
                        if uu____62208
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___973_62219 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___973_62219.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___973_62219.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___976_62220 = lb  in
                      let uu____62221 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___976_62220.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___976_62220.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____62221;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___976_62220.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___976_62220.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____62253  -> fun env1  -> dummy :: env1)
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
            (fun uu____62345  ->
               let uu____62346 = FStar_Syntax_Print.tag_of_term t  in
               let uu____62348 = env_to_string env  in
               let uu____62350 = stack_to_string stack  in
               let uu____62352 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____62346 uu____62348 uu____62350 uu____62352);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____62359,uu____62360),aq,r))::stack1
               ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____62441 = close_binders cfg env' bs  in
               (match uu____62441 with
                | (bs1,uu____62457) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____62477 =
                      let uu___1034_62480 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___1034_62480.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___1034_62480.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____62477)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____62536 =
                 match uu____62536 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____62651 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____62682 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____62771  ->
                                     fun uu____62772  ->
                                       match (uu____62771, uu____62772) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____62922 = norm_pat env4 p1
                                              in
                                           (match uu____62922 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____62682 with
                            | (pats1,env4) ->
                                ((let uu___1071_63092 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___1071_63092.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___1075_63113 = x  in
                             let uu____63114 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1075_63113.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1075_63113.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____63114
                             }  in
                           ((let uu___1078_63128 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___1078_63128.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___1082_63139 = x  in
                             let uu____63140 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1082_63139.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1082_63139.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____63140
                             }  in
                           ((let uu___1085_63154 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___1085_63154.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___1091_63170 = x  in
                             let uu____63171 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1091_63170.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1091_63170.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____63171
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___1095_63188 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___1095_63188.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____63193 = norm_pat env2 pat  in
                     (match uu____63193 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____63262 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____63262
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____63281 =
                   let uu____63282 =
                     let uu____63305 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____63305)  in
                   FStar_Syntax_Syntax.Tm_match uu____63282  in
                 mk uu____63281 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____63420 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____63529  ->
                                       match uu____63529 with
                                       | (a,q) ->
                                           let uu____63556 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____63556, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____63420
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____63569 =
                       let uu____63576 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____63576)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____63569
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____63588 =
                       let uu____63597 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____63597)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____63588
                 | uu____63602 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____63608 -> failwith "Impossible: unexpected stack element")

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
            let uu____63624 =
              let uu____63625 = inline_closure_env cfg env [] t  in
              FStar_Syntax_Syntax.Meta uu____63625  in
            FStar_Pervasives_Native.Some uu____63624
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
        let uu____63642 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____63726  ->
                  fun uu____63727  ->
                    match (uu____63726, uu____63727) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___1148_63867 = b  in
                          let uu____63868 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1148_63867.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1148_63867.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____63868
                          }  in
                        let imp1 = close_imp cfg env1 imp  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp1) :: out))) (env, []))
           in
        match uu____63642 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____64010 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____64023 = inline_closure_env cfg env [] t  in
                 let uu____64024 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____64023 uu____64024
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____64037 = inline_closure_env cfg env [] t  in
                 let uu____64038 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____64037 uu____64038
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____64092  ->
                           match uu____64092 with
                           | (a,q) ->
                               let uu____64113 =
                                 inline_closure_env cfg env [] a  in
                               (uu____64113, q)))
                    in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___590_64130  ->
                           match uu___590_64130 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____64134 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____64134
                           | f -> f))
                    in
                 let uu____64138 =
                   let uu___1181_64139 = c1  in
                   let uu____64140 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____64140;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___1181_64139.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____64138)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___591_64150  ->
            match uu___591_64150 with
            | FStar_Syntax_Syntax.DECREASES uu____64152 -> false
            | uu____64156 -> true))

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
                   (fun uu___592_64175  ->
                      match uu___592_64175 with
                      | FStar_Syntax_Syntax.DECREASES uu____64177 -> false
                      | uu____64181 -> true))
               in
            let rc1 =
              let uu___1198_64184 = rc  in
              let uu____64185 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___1198_64184.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____64185;
                FStar_Syntax_Syntax.residual_flags = flags
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____64194 -> lopt

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
    let uu____64242 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____64242 with
    | FStar_Pervasives_Native.Some e ->
        let uu____64281 = FStar_Syntax_Embeddings.unembed e t  in
        uu____64281 true FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____64301 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv * 'Auu____64301)
        FStar_Pervasives_Native.option * closure) Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____64363  ->
           fun subst1  ->
             match uu____64363 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____64404,uu____64405)) ->
                      let uu____64466 = b  in
                      (match uu____64466 with
                       | (bv,uu____64474) ->
                           let uu____64475 =
                             let uu____64477 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____64477  in
                           if uu____64475
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____64485 = unembed_binder term1  in
                              match uu____64485 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____64492 =
                                      let uu___1233_64493 = bv  in
                                      let uu____64494 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___1233_64493.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___1233_64493.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____64494
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____64492
                                     in
                                  let b_for_x =
                                    let uu____64500 =
                                      let uu____64507 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____64507)
                                       in
                                    FStar_Syntax_Syntax.NT uu____64500  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___593_64523  ->
                                         match uu___593_64523 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____64525,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____64527;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____64528;_})
                                             ->
                                             let uu____64533 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____64533
                                         | uu____64535 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____64537 -> subst1)) env []
  
let reduce_primops :
  'Auu____64559 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'Auu____64559)
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
            (let uu____64611 = FStar_Syntax_Util.head_and_args tm  in
             match uu____64611 with
             | (head1,args) ->
                 let uu____64656 =
                   let uu____64657 = FStar_Syntax_Util.un_uinst head1  in
                   uu____64657.FStar_Syntax_Syntax.n  in
                 (match uu____64656 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____64663 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                      (match uu____64663 with
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
                                (fun uu____64686  ->
                                   let uu____64687 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name
                                      in
                                   let uu____64689 =
                                     FStar_Util.string_of_int l  in
                                   let uu____64691 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____64687 uu____64689 uu____64691);
                              tm)
                           else
                             (let uu____64696 =
                                if l = prim_step.FStar_TypeChecker_Cfg.arity
                                then (args, [])
                                else
                                  FStar_List.splitAt
                                    prim_step.FStar_TypeChecker_Cfg.arity
                                    args
                                 in
                              match uu____64696 with
                              | (args_1,args_2) ->
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____64782  ->
                                        let uu____64783 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____64783);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____64788  ->
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
                                           (fun uu____64802  ->
                                              let uu____64803 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____64803);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____64811  ->
                                              let uu____64812 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____64814 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____64812 uu____64814);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____64817 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____64821  ->
                                 let uu____64822 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____64822);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____64828  ->
                            let uu____64829 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____64829);
                       (match args with
                        | (a1,uu____64835)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____64860 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____64874  ->
                            let uu____64875 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____64875);
                       (match args with
                        | (t,uu____64881)::(r,uu____64883)::[] ->
                            let uu____64924 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____64924 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____64930 -> tm))
                  | uu____64941 -> tm))
  
let reduce_equality :
  'Auu____64952 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'Auu____64952)
          FStar_Pervasives_Native.option * closure) Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun tm  ->
        reduce_primops norm_cb
          (let uu___1321_65001 = cfg  in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___1323_65004 = FStar_TypeChecker_Cfg.default_steps  in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.nbe_step);
                  FStar_TypeChecker_Cfg.for_extraction =
                    (uu___1323_65004.FStar_TypeChecker_Cfg.for_extraction)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___1321_65001.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___1321_65001.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___1321_65001.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___1321_65001.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___1321_65001.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___1321_65001.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___1321_65001.FStar_TypeChecker_Cfg.reifying)
           }) tm
  
type norm_request_t =
  | Norm_request_none 
  | Norm_request_ready 
  | Norm_request_requires_rejig 
let (uu___is_Norm_request_none : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_none  -> true | uu____65015 -> false
  
let (uu___is_Norm_request_ready : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_ready  -> true | uu____65026 -> false
  
let (uu___is_Norm_request_requires_rejig : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Norm_request_requires_rejig  -> true
    | uu____65037 -> false
  
let (is_norm_request :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.args -> norm_request_t) =
  fun hd1  ->
    fun args  ->
      let aux min_args =
        let uu____65058 = FStar_All.pipe_right args FStar_List.length  in
        FStar_All.pipe_right uu____65058
          (fun n1  ->
             if n1 < min_args
             then Norm_request_none
             else
               if n1 = min_args
               then Norm_request_ready
               else Norm_request_requires_rejig)
         in
      let uu____65090 =
        let uu____65091 = FStar_Syntax_Util.un_uinst hd1  in
        uu____65091.FStar_Syntax_Syntax.n  in
      match uu____65090 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          -> aux (Prims.parse_int "2")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          aux (Prims.parse_int "1")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          aux (Prims.parse_int "3")
      | uu____65100 -> Norm_request_none
  
let (should_consider_norm_requests : FStar_TypeChecker_Cfg.cfg -> Prims.bool)
  =
  fun cfg  ->
    (Prims.op_Negation
       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
      &&
      (let uu____65109 =
         FStar_Ident.lid_equals
           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
           FStar_Parser_Const.prims_lid
          in
       Prims.op_Negation uu____65109)
  
let (rejig_norm_request :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term)
  =
  fun hd1  ->
    fun args  ->
      let uu____65122 =
        let uu____65123 = FStar_Syntax_Util.un_uinst hd1  in
        uu____65123.FStar_Syntax_Syntax.n  in
      match uu____65122 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          ->
          (match args with
           | t1::t2::rest when
               (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____65181 = FStar_Syntax_Util.mk_app hd1 [t1; t2]  in
               FStar_Syntax_Util.mk_app uu____65181 rest
           | uu____65208 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize_term")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          (match args with
           | t::rest when (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____65248 = FStar_Syntax_Util.mk_app hd1 [t]  in
               FStar_Syntax_Util.mk_app uu____65248 rest
           | uu____65267 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          (match args with
           | t1::t2::t3::rest when
               (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____65341 = FStar_Syntax_Util.mk_app hd1 [t1; t2; t3]
                  in
               FStar_Syntax_Util.mk_app uu____65341 rest
           | uu____65376 ->
               failwith "Impossible! invalid rejig_norm_request for norm")
      | uu____65378 ->
          let uu____65379 =
            let uu____65381 = FStar_Syntax_Print.term_to_string hd1  in
            FStar_String.op_Hat
              "Impossible! invalid rejig_norm_request for: %s" uu____65381
             in
          failwith uu____65379
  
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s  ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
  
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___594_65402  ->
    match uu___594_65402 with
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
        let uu____65409 =
          let uu____65412 =
            let uu____65413 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            FStar_TypeChecker_Env.UnfoldOnly uu____65413  in
          [uu____65412]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____65409
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____65421 =
          let uu____65424 =
            let uu____65425 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            FStar_TypeChecker_Env.UnfoldFully uu____65425  in
          [uu____65424]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____65421
    | FStar_Syntax_Embeddings.UnfoldAttr names1 ->
        let uu____65433 =
          let uu____65436 =
            let uu____65437 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            FStar_TypeChecker_Env.UnfoldAttr uu____65437  in
          [uu____65436]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____65433
    | FStar_Syntax_Embeddings.NBE  -> [FStar_TypeChecker_Env.NBE]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  = fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____65462 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term * 'Auu____65462) Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list * FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____65513 =
            let uu____65518 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____65518 s  in
          match uu____65513 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____65534 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____65534
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
        | uu____65569::(tm,uu____65571)::[] ->
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
        | (tm,uu____65600)::[] ->
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
        | (steps,uu____65621)::uu____65622::(tm,uu____65624)::[] ->
            let add_exclude s z =
              let uu____65662 =
                FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s  in
              if uu____65662
              then s
              else (FStar_TypeChecker_Env.Exclude z) :: s  in
            let uu____65669 =
              let uu____65674 = full_norm steps  in parse_steps uu____65674
               in
            (match uu____65669 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = FStar_TypeChecker_Env.Beta :: s  in
                 let s2 = add_exclude s1 FStar_TypeChecker_Env.Zeta  in
                 let s3 = add_exclude s2 FStar_TypeChecker_Env.Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____65713 -> FStar_Pervasives_Native.None
  
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun s  ->
      fun tm  ->
        let delta_level =
          let uu____65745 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___595_65752  ->
                    match uu___595_65752 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____65754 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____65756 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____65760 -> true
                    | uu____65764 -> false))
             in
          if uu____65745
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta]  in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____65774  ->
             let uu____65775 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____65775);
        (let tm_norm =
           let uu____65779 =
             let uu____65794 = FStar_TypeChecker_Cfg.cfg_env cfg  in
             uu____65794.FStar_TypeChecker_Env.nbe  in
           uu____65779 s cfg.FStar_TypeChecker_Cfg.tcenv tm  in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____65798  ->
              let uu____65799 = FStar_Syntax_Print.term_to_string tm_norm  in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____65799);
         tm_norm)
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___596_65810  ->
    match uu___596_65810 with
    | (App
        (uu____65814,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____65815;
                       FStar_Syntax_Syntax.vars = uu____65816;_},uu____65817,uu____65818))::uu____65819
        -> true
    | uu____65825 -> false
  
let firstn :
  'Auu____65836 .
    Prims.int ->
      'Auu____65836 Prims.list ->
        ('Auu____65836 Prims.list * 'Auu____65836 Prims.list)
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack  ->
      let rec drop_irrel uu___597_65893 =
        match uu___597_65893 with
        | (MemoLazy uu____65898)::s -> drop_irrel s
        | (UnivArgs uu____65908)::s -> drop_irrel s
        | s -> s  in
      let uu____65921 = drop_irrel stack  in
      match uu____65921 with
      | (App
          (uu____65925,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____65926;
                         FStar_Syntax_Syntax.vars = uu____65927;_},uu____65928,uu____65929))::uu____65930
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____65935 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____65964) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____65974) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____65995  ->
                  match uu____65995 with
                  | (a,uu____66006) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____66017 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____66042 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____66044 -> false
    | FStar_Syntax_Syntax.Tm_type uu____66058 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____66060 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____66062 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____66064 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____66066 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____66069 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____66077 -> false
    | FStar_Syntax_Syntax.Tm_let uu____66085 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____66100 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____66120 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____66136 -> true
    | FStar_Syntax_Syntax.Tm_match uu____66144 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____66216  ->
                   match uu____66216 with
                   | (a,uu____66227) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____66238) ->
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
                     (fun uu____66370  ->
                        match uu____66370 with
                        | (a,uu____66381) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____66390,uu____66391,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____66397,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____66403 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____66413 -> false
            | FStar_Syntax_Syntax.Meta_named uu____66415 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____66426 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____66437 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Should_unfold_fully  -> true
    | uu____66448 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Should_unfold_reify  -> true
    | uu____66459 -> false
  
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
            let uu____66492 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo
               in
            match uu____66492 with
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
              (fun uu____66691  ->
                 fun uu____66692  ->
                   match (uu____66691, uu____66692) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____66798 =
            match uu____66798 with
            | (x,y,z) ->
                let uu____66818 = FStar_Util.string_of_bool x  in
                let uu____66820 = FStar_Util.string_of_bool y  in
                let uu____66822 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____66818 uu____66820
                  uu____66822
             in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg  in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____66850  ->
                    let uu____66851 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____66853 = FStar_Util.string_of_bool b  in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____66851 uu____66853);
               if b then reif else no)
            else
              if
                (let uu____66868 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                 FStar_Option.isSome uu____66868)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____66873  ->
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
                          ((is_rec,uu____66908),uu____66909);
                        FStar_Syntax_Syntax.sigrng = uu____66910;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____66912;
                        FStar_Syntax_Syntax.sigattrs = uu____66913;_},uu____66914),uu____66915),uu____66916,uu____66917,uu____66918)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____67025  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____67027,uu____67028,uu____67029,uu____67030) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____67097  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____67100),uu____67101);
                        FStar_Syntax_Syntax.sigrng = uu____67102;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____67104;
                        FStar_Syntax_Syntax.sigattrs = uu____67105;_},uu____67106),uu____67107),uu____67108,uu____67109,uu____67110)
                     when
                     is_rec &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____67217  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____67219,FStar_Pervasives_Native.Some
                    uu____67220,uu____67221,uu____67222) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____67290  ->
                           let uu____67291 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____67291);
                      (let uu____67294 =
                         let uu____67306 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____67332 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____67332
                            in
                         let uu____67344 =
                           let uu____67356 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____67382 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____67382
                              in
                           let uu____67398 =
                             let uu____67410 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____67436 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____67436
                                in
                             [uu____67410]  in
                           uu____67356 :: uu____67398  in
                         uu____67306 :: uu____67344  in
                       comb_or uu____67294))
                 | (uu____67484,uu____67485,FStar_Pervasives_Native.Some
                    uu____67486,uu____67487) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____67555  ->
                           let uu____67556 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____67556);
                      (let uu____67559 =
                         let uu____67571 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____67597 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____67597
                            in
                         let uu____67609 =
                           let uu____67621 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____67647 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____67647
                              in
                           let uu____67663 =
                             let uu____67675 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____67701 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____67701
                                in
                             [uu____67675]  in
                           uu____67621 :: uu____67663  in
                         uu____67571 :: uu____67609  in
                       comb_or uu____67559))
                 | (uu____67749,uu____67750,uu____67751,FStar_Pervasives_Native.Some
                    uu____67752) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____67820  ->
                           let uu____67821 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____67821);
                      (let uu____67824 =
                         let uu____67836 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____67862 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____67862
                            in
                         let uu____67874 =
                           let uu____67886 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____67912 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____67912
                              in
                           let uu____67928 =
                             let uu____67940 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____67966 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____67966
                                in
                             [uu____67940]  in
                           uu____67886 :: uu____67928  in
                         uu____67836 :: uu____67874  in
                       comb_or uu____67824))
                 | uu____68014 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____68060  ->
                           let uu____68061 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____68063 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____68065 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level
                              in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____68061 uu____68063 uu____68065);
                      (let uu____68068 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___598_68074  ->
                                 match uu___598_68074 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.InliningDelta  ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____68080 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv
                                        in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____68080 l))
                          in
                       FStar_All.pipe_left yesno uu____68068)))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____68096  ->
               let uu____68097 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____68099 =
                 let uu____68101 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____68101  in
               let uu____68102 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____68097 uu____68099 uu____68102);
          (match res with
           | (false ,uu____68105,uu____68106) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____68131 ->
               let uu____68141 =
                 let uu____68143 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____68143
                  in
               FStar_All.pipe_left failwith uu____68141)
  
let decide_unfolding :
  'Auu____68162 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'Auu____68162 ->
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
                    let uu___1740_68231 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___1742_68234 =
                           cfg.FStar_TypeChecker_Cfg.steps  in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1742_68234.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1742_68234.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1742_68234.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1742_68234.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1742_68234.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1742_68234.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1742_68234.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___1742_68234.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1742_68234.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1742_68234.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1742_68234.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1742_68234.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1742_68234.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1742_68234.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1742_68234.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1742_68234.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1742_68234.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1742_68234.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___1742_68234.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1742_68234.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1742_68234.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1742_68234.FStar_TypeChecker_Cfg.for_extraction)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1740_68231.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1740_68231.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___1740_68231.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1740_68231.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1740_68231.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1740_68231.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1740_68231.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1740_68231.FStar_TypeChecker_Cfg.reifying)
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
                        let uu____68296 = push1 e t  in (UnivArgs (us, r)) ::
                          uu____68296
                    | h::t -> e :: h :: t  in
                  let ref =
                    let uu____68308 =
                      let uu____68315 =
                        let uu____68316 =
                          let uu____68317 = FStar_Syntax_Syntax.lid_of_fv fv
                             in
                          FStar_Const.Const_reflect uu____68317  in
                        FStar_Syntax_Syntax.Tm_constant uu____68316  in
                      FStar_Syntax_Syntax.mk uu____68315  in
                    uu____68308 FStar_Pervasives_Native.None
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
    let uu____68383 =
      let uu____68384 = FStar_Syntax_Subst.compress t  in
      uu____68384.FStar_Syntax_Syntax.n  in
    match uu____68383 with
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____68415 =
          let uu____68416 = FStar_Syntax_Util.un_uinst hd1  in
          uu____68416.FStar_Syntax_Syntax.n  in
        (match uu____68415 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStar_List.length args) = (Prims.parse_int "3"))
             ->
             let f =
               let uu____68433 =
                 let uu____68440 =
                   let uu____68451 = FStar_All.pipe_right args FStar_List.tl
                      in
                   FStar_All.pipe_right uu____68451 FStar_List.tl  in
                 FStar_All.pipe_right uu____68440 FStar_List.hd  in
               FStar_All.pipe_right uu____68433 FStar_Pervasives_Native.fst
                in
             FStar_Pervasives_Native.Some f
         | uu____68550 -> FStar_Pervasives_Native.None)
    | uu____68551 -> FStar_Pervasives_Native.None
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____68830 ->
                   let uu____68853 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____68853
               | uu____68856 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____68866  ->
               let uu____68867 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____68869 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____68871 = FStar_Syntax_Print.term_to_string t1  in
               let uu____68873 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____68881 =
                 let uu____68883 =
                   let uu____68886 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____68886
                    in
                 stack_to_string uu____68883  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____68867 uu____68869 uu____68871 uu____68873 uu____68881);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____68914  ->
               let uu____68915 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____68915);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____68921  ->
                     let uu____68922 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____68922);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____68925 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____68929  ->
                     let uu____68930 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____68930);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____68933 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____68937  ->
                     let uu____68938 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____68938);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____68941 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____68945  ->
                     let uu____68946 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____68946);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____68949;
                 FStar_Syntax_Syntax.fv_delta = uu____68950;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____68954  ->
                     let uu____68955 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____68955);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____68958;
                 FStar_Syntax_Syntax.fv_delta = uu____68959;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____68960);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____68970  ->
                     let uu____68971 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____68971);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid
                  in
               let uu____68977 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
               (match uu____68977 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level _68980) when
                    _68980 = (Prims.parse_int "0") ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____68984  ->
                          let uu____68985 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____68985);
                     rebuild cfg env stack t1)
                | uu____68988 ->
                    let uu____68991 =
                      decide_unfolding cfg env stack
                        t1.FStar_Syntax_Syntax.pos fv qninfo
                       in
                    (match uu____68991 with
                     | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                         do_unfold_fv cfg1 env stack1 t1 qninfo fv
                     | FStar_Pervasives_Native.None  ->
                         rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_quoted uu____69018 ->
               let uu____69025 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____69025
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____69053 = is_norm_request hd1 args  in
                  uu____69053 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu____69059 = rejig_norm_request hd1 args  in
                 norm cfg env stack uu____69059))
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____69087 = is_norm_request hd1 args  in
                  uu____69087 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___1850_69094 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1852_69097 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1852_69097.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1852_69097.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1852_69097.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___1852_69097.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1852_69097.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1852_69097.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1852_69097.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1852_69097.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1852_69097.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1852_69097.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1852_69097.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1852_69097.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1852_69097.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1852_69097.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1852_69097.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1852_69097.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1852_69097.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1852_69097.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1852_69097.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1852_69097.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1852_69097.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1852_69097.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1852_69097.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1850_69094.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1850_69094.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1850_69094.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1850_69094.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1850_69094.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1850_69094.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____69104 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____69104 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____69140  ->
                                 fun stack1  ->
                                   match uu____69140 with
                                   | (a,aq) ->
                                       let uu____69152 =
                                         let uu____69153 =
                                           let uu____69160 =
                                             let uu____69161 =
                                               let uu____69193 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____69193, false)
                                                in
                                             Clos uu____69161  in
                                           (uu____69160, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____69153  in
                                       uu____69152 :: stack1) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____69261  ->
                            let uu____69262 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____69262);
                       norm cfg env stack1 hd1))
                 | FStar_Pervasives_Native.Some (s,tm) when is_nbe_request s
                     ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____69289 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting NBE request on %s ... \n" uu____69289)
                      else ();
                      (let tm' = closure_as_term cfg env tm  in
                       let start = FStar_Util.now ()  in
                       let tm_norm = nbe_eval cfg s tm'  in
                       let fin = FStar_Util.now ()  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         (let uu____69300 =
                            let uu____69302 =
                              let uu____69304 =
                                FStar_Util.time_diff start fin  in
                              FStar_Pervasives_Native.snd uu____69304  in
                            FStar_Util.string_of_int uu____69302  in
                          let uu____69311 =
                            FStar_Syntax_Print.term_to_string tm'  in
                          let uu____69313 =
                            FStar_Syntax_Print.term_to_string tm_norm  in
                          FStar_Util.print3 "NBE'd (%s ms) %s\n\tto %s\n"
                            uu____69300 uu____69311 uu____69313)
                       else ();
                       norm cfg env stack tm_norm))
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____69332 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting norm request on %s ... \n" uu____69332)
                      else ();
                      (let delta_level =
                         let uu____69340 =
                           FStar_All.pipe_right s
                             (FStar_Util.for_some
                                (fun uu___599_69347  ->
                                   match uu___599_69347 with
                                   | FStar_TypeChecker_Env.UnfoldUntil
                                       uu____69349 -> true
                                   | FStar_TypeChecker_Env.UnfoldOnly
                                       uu____69351 -> true
                                   | FStar_TypeChecker_Env.UnfoldFully
                                       uu____69355 -> true
                                   | uu____69359 -> false))
                            in
                         if uu____69340
                         then
                           [FStar_TypeChecker_Env.Unfold
                              FStar_Syntax_Syntax.delta_constant]
                         else [FStar_TypeChecker_Env.NoDelta]  in
                       let cfg'1 =
                         let uu___1893_69367 = cfg  in
                         let uu____69368 =
                           let uu___1895_69369 =
                             FStar_TypeChecker_Cfg.to_fsteps s  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.unfold_only);
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               true;
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___1895_69369.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         {
                           FStar_TypeChecker_Cfg.steps = uu____69368;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___1893_69367.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___1893_69367.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = delta_level;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___1893_69367.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong =
                             (uu___1893_69367.FStar_TypeChecker_Cfg.strong);
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___1893_69367.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___1893_69367.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let stack' =
                         let tail1 = (Cfg cfg) :: stack  in
                         if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           let uu____69377 =
                             let uu____69378 =
                               let uu____69383 = FStar_Util.now ()  in
                               (t1, uu____69383)  in
                             Debug uu____69378  in
                           uu____69377 :: tail1
                         else tail1  in
                       norm cfg'1 env stack' tm))))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____69388 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____69388
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____69399 =
                      let uu____69406 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____69406, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____69399  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____69415 = lookup_bvar env x  in
               (match uu____69415 with
                | Univ uu____69416 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                    then
                      let uu____69470 = FStar_ST.op_Bang r  in
                      (match uu____69470 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____69566  ->
                                 let uu____69567 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____69569 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____69567
                                   uu____69569);
                            (let uu____69572 = maybe_weakly_reduced t'  in
                             if uu____69572
                             then
                               match stack with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____69575 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____69619)::uu____69620 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____69631,uu____69632))::stack_rest ->
                    (match c with
                     | Univ uu____69636 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____69645 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____69675  ->
                                    let uu____69676 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____69676);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____69712  ->
                                    let uu____69713 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____69713);
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
                       (fun uu____69761  ->
                          let uu____69762 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____69762);
                     norm cfg env stack1 t1)
                | (Match uu____69765)::uu____69766 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____69781 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____69781 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____69817  -> dummy :: env1) env)
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
                                          let uu____69861 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____69861)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_69869 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_69869.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_69869.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____69870 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____69876  ->
                                 let uu____69877 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____69877);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_69892 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_69892.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_69892.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_69892.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_69892.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_69892.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_69892.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_69892.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_69892.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____69896)::uu____69897 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____69908 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____69908 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____69944  -> dummy :: env1) env)
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
                                          let uu____69988 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____69988)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_69996 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_69996.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_69996.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____69997 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____70003  ->
                                 let uu____70004 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____70004);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_70019 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_70019.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_70019.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_70019.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_70019.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_70019.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_70019.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_70019.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_70019.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____70023)::uu____70024 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____70037 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____70037 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____70073  -> dummy :: env1) env)
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
                                          let uu____70117 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____70117)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_70125 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_70125.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_70125.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____70126 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____70132  ->
                                 let uu____70133 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____70133);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_70148 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_70148.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_70148.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_70148.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_70148.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_70148.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_70148.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_70148.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_70148.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____70152)::uu____70153 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____70168 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____70168 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____70204  -> dummy :: env1) env)
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
                                          let uu____70248 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____70248)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_70256 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_70256.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_70256.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____70257 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____70263  ->
                                 let uu____70264 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____70264);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_70279 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_70279.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_70279.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_70279.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_70279.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_70279.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_70279.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_70279.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_70279.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____70283)::uu____70284 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____70299 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____70299 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____70335  -> dummy :: env1) env)
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
                                          let uu____70379 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____70379)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_70387 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_70387.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_70387.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____70388 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____70394  ->
                                 let uu____70395 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____70395);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_70410 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_70410.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_70410.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_70410.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_70410.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_70410.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_70410.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_70410.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_70410.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____70414)::uu____70415 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____70434 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____70434 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____70470  -> dummy :: env1) env)
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
                                          let uu____70514 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____70514)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_70522 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_70522.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_70522.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____70523 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____70529  ->
                                 let uu____70530 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____70530);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_70545 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_70545.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_70545.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_70545.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_70545.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_70545.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_70545.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_70545.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_70545.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____70553 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____70553 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____70589  -> dummy :: env1) env)
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
                                          let uu____70633 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____70633)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_70641 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_70641.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_70641.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____70642 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____70648  ->
                                 let uu____70649 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____70649);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_70664 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_70664.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_70664.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_70664.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_70664.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_70664.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_70664.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_70664.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_70664.FStar_TypeChecker_Cfg.reifying)
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
                      (fun uu____70708  ->
                         fun stack1  ->
                           match uu____70708 with
                           | (a,aq) ->
                               let uu____70720 =
                                 let uu____70721 =
                                   let uu____70728 =
                                     let uu____70729 =
                                       let uu____70761 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____70761, false)  in
                                     Clos uu____70729  in
                                   (uu____70728, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____70721  in
                               uu____70720 :: stack1) args)
                  in
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____70829  ->
                     let uu____70830 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____70830);
                norm cfg env stack1 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,uu____70844) when
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
                             ((let uu___2047_70889 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2047_70889.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2047_70889.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____70890 ->
                      let uu____70905 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____70905)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____70909 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____70909 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____70940 =
                          let uu____70941 =
                            let uu____70948 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___2056_70954 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2056_70954.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___2056_70954.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____70948)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____70941  in
                        mk uu____70940 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____70978 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____70978
               else
                 (let uu____70981 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____70981 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____70989 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____71015  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____70989 c1  in
                      let t2 =
                        let uu____71039 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____71039 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____71152)::uu____71153 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____71166  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____71168)::uu____71169 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____71180  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____71182,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____71183;
                                   FStar_Syntax_Syntax.vars = uu____71184;_},uu____71185,uu____71186))::uu____71187
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____71194  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____71196)::uu____71197 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____71208  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____71210 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____71213  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____71218  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____71244 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____71244
                         | FStar_Util.Inr c ->
                             let uu____71258 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____71258
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____71281 =
                               let uu____71282 =
                                 let uu____71309 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____71309, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____71282
                                in
                             mk uu____71281 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____71344 ->
                           let uu____71345 =
                             let uu____71346 =
                               let uu____71347 =
                                 let uu____71374 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____71374, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____71347
                                in
                             mk uu____71346 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____71345))))
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
                   let uu___2135_71452 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___2137_71455 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___2137_71455.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___2135_71452.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___2135_71452.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___2135_71452.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___2135_71452.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___2135_71452.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___2135_71452.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___2135_71452.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___2135_71452.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____71496 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____71496 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___2150_71516 = cfg  in
                               let uu____71517 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2150_71516.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____71517;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2150_71516.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2150_71516.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2150_71516.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___2150_71516.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2150_71516.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2150_71516.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2150_71516.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____71524 =
                                 let uu____71525 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____71525  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____71524
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___2157_71528 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___2157_71528.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2157_71528.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2157_71528.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2157_71528.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____71529 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____71529
           | FStar_Syntax_Syntax.Tm_let
               ((uu____71542,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____71543;
                               FStar_Syntax_Syntax.lbunivs = uu____71544;
                               FStar_Syntax_Syntax.lbtyp = uu____71545;
                               FStar_Syntax_Syntax.lbeff = uu____71546;
                               FStar_Syntax_Syntax.lbdef = uu____71547;
                               FStar_Syntax_Syntax.lbattrs = uu____71548;
                               FStar_Syntax_Syntax.lbpos = uu____71549;_}::uu____71550),uu____71551)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name
                   cfg.FStar_TypeChecker_Cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____71597 =
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
               if uu____71597
               then
                 let binder =
                   let uu____71601 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____71601  in
                 let env1 =
                   let uu____71611 =
                     let uu____71618 =
                       let uu____71619 =
                         let uu____71651 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____71651,
                           false)
                          in
                       Clos uu____71619  in
                     ((FStar_Pervasives_Native.Some binder), uu____71618)  in
                   uu____71611 :: env  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____71726  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                 then
                   (FStar_TypeChecker_Cfg.log cfg
                      (fun uu____71733  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____71735 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____71735))
                 else
                   (let uu____71738 =
                      let uu____71743 =
                        let uu____71744 =
                          let uu____71751 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____71751
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____71744]  in
                      FStar_Syntax_Subst.open_term uu____71743 body  in
                    match uu____71738 with
                    | (bs,body1) ->
                        (FStar_TypeChecker_Cfg.log cfg
                           (fun uu____71778  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____71787 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____71787  in
                            FStar_Util.Inl
                              (let uu___2199_71803 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2199_71803.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2199_71803.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____71806  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___2204_71809 = lb  in
                             let uu____71810 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___2204_71809.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2204_71809.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____71810;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2204_71809.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2204_71809.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____71839  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___2211_71864 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps =
                                 (uu___2211_71864.FStar_TypeChecker_Cfg.steps);
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___2211_71864.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___2211_71864.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 (uu___2211_71864.FStar_TypeChecker_Cfg.delta_level);
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___2211_71864.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong = true;
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___2211_71864.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___2211_71864.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___2211_71864.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           FStar_TypeChecker_Cfg.log cfg1
                             (fun uu____71868  ->
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
               let uu____71889 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____71889 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____71925 =
                               let uu___2227_71926 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2227_71926.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2227_71926.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____71925  in
                           let uu____71927 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____71927 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____71953 =
                                   FStar_List.map (fun uu____71969  -> dummy)
                                     lbs1
                                    in
                                 let uu____71970 =
                                   let uu____71979 =
                                     FStar_List.map
                                       (fun uu____72001  -> dummy) xs1
                                      in
                                   FStar_List.append uu____71979 env  in
                                 FStar_List.append uu____71953 uu____71970
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____72027 =
                                       let uu___2241_72028 = rc  in
                                       let uu____72029 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___2241_72028.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____72029;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___2241_72028.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____72027
                                 | uu____72038 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___2246_72044 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___2246_72044.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___2246_72044.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___2246_72044.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___2246_72044.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____72054 =
                        FStar_List.map (fun uu____72070  -> dummy) lbs2  in
                      FStar_List.append uu____72054 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____72078 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____72078 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___2255_72094 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___2255_72094.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___2255_72094.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
               ->
               let uu____72128 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____72128
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____72149 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____72227  ->
                        match uu____72227 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___2271_72352 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2271_72352.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___2271_72352.FStar_Syntax_Syntax.sort)
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
               (match uu____72149 with
                | (rec_env,memos,uu____72543) ->
                    let uu____72598 =
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
                             let uu____72847 =
                               let uu____72854 =
                                 let uu____72855 =
                                   let uu____72887 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____72887, false)
                                    in
                                 Clos uu____72855  in
                               (FStar_Pervasives_Native.None, uu____72854)
                                in
                             uu____72847 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____72972  ->
                     let uu____72973 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____72973);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____72997 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____73001::uu____73002 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____73007) ->
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
                             | uu____73038 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____73054 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____73054
                              | uu____73067 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____73073 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____73097 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____73111 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____73125 =
                        let uu____73127 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____73129 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____73127 uu____73129
                         in
                      failwith uu____73125
                    else
                      (let uu____73134 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____73134)
                | uu____73135 -> norm cfg env stack t2))

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
              let uu____73144 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____73144 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____73158  ->
                        let uu____73159 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____73159);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____73172  ->
                        let uu____73173 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____73175 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____73173 uu____73175);
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
                      | (UnivArgs (us',uu____73188))::stack1 ->
                          ((let uu____73197 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____73197
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____73205 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____73205) us'
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
                      | uu____73241 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____73244 ->
                          let uu____73247 =
                            let uu____73249 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____73249
                             in
                          failwith uu____73247
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
                  let uu___2377_73277 = cfg  in
                  let uu____73278 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____73278;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___2377_73277.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___2377_73277.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___2377_73277.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___2377_73277.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___2377_73277.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___2377_73277.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___2377_73277.FStar_TypeChecker_Cfg.reifying)
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
                     (uu____73309,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____73310;
                                    FStar_Syntax_Syntax.vars = uu____73311;_},uu____73312,uu____73313))::uu____73314
                     -> ()
                 | uu____73319 ->
                     let uu____73322 =
                       let uu____73324 = stack_to_string stack  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____73324
                        in
                     failwith uu____73322);
                (let head0 = head1  in
                 let head2 = FStar_Syntax_Util.unascribe head1  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____73333  ->
                      let uu____73334 = FStar_Syntax_Print.tag_of_term head2
                         in
                      let uu____73336 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____73334
                        uu____73336);
                 (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                  let uu____73340 =
                    let uu____73341 = FStar_Syntax_Subst.compress head3  in
                    uu____73341.FStar_Syntax_Syntax.n  in
                  match uu____73340 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let ed =
                        let uu____73362 =
                          FStar_TypeChecker_Env.norm_eff_name
                            cfg.FStar_TypeChecker_Cfg.tcenv m
                           in
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv uu____73362
                         in
                      let uu____73363 = ed.FStar_Syntax_Syntax.bind_repr  in
                      (match uu____73363 with
                       | (uu____73364,bind_repr) ->
                           (match lb.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____73374 ->
                                failwith
                                  "Cannot reify a top-level let binding"
                            | FStar_Util.Inl x ->
                                let is_return e =
                                  let uu____73385 =
                                    let uu____73386 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____73386.FStar_Syntax_Syntax.n  in
                                  match uu____73385 with
                                  | FStar_Syntax_Syntax.Tm_meta
                                      (e1,FStar_Syntax_Syntax.Meta_monadic
                                       (uu____73392,uu____73393))
                                      ->
                                      let uu____73402 =
                                        let uu____73403 =
                                          FStar_Syntax_Subst.compress e1  in
                                        uu____73403.FStar_Syntax_Syntax.n  in
                                      (match uu____73402 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                            (uu____73409,msrc,uu____73411))
                                           when
                                           FStar_Syntax_Util.is_pure_effect
                                             msrc
                                           ->
                                           let uu____73420 =
                                             FStar_Syntax_Subst.compress e2
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____73420
                                       | uu____73421 ->
                                           FStar_Pervasives_Native.None)
                                  | uu____73422 ->
                                      FStar_Pervasives_Native.None
                                   in
                                let uu____73423 =
                                  is_return lb.FStar_Syntax_Syntax.lbdef  in
                                (match uu____73423 with
                                 | FStar_Pervasives_Native.Some e ->
                                     let lb1 =
                                       let uu___2449_73428 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___2449_73428.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___2449_73428.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           (uu___2449_73428.FStar_Syntax_Syntax.lbtyp);
                                         FStar_Syntax_Syntax.lbeff =
                                           FStar_Parser_Const.effect_PURE_lid;
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___2449_73428.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___2449_73428.FStar_Syntax_Syntax.lbpos)
                                       }  in
                                     let uu____73429 = FStar_List.tl stack
                                        in
                                     let uu____73430 =
                                       let uu____73431 =
                                         let uu____73438 =
                                           let uu____73439 =
                                             let uu____73453 =
                                               FStar_Syntax_Util.mk_reify
                                                 body
                                                in
                                             ((false, [lb1]), uu____73453)
                                              in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____73439
                                            in
                                         FStar_Syntax_Syntax.mk uu____73438
                                          in
                                       uu____73431
                                         FStar_Pervasives_Native.None
                                         head3.FStar_Syntax_Syntax.pos
                                        in
                                     norm cfg env uu____73429 uu____73430
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____73469 =
                                       let uu____73471 = is_return body  in
                                       match uu____73471 with
                                       | FStar_Pervasives_Native.Some
                                           {
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_bvar y;
                                             FStar_Syntax_Syntax.pos =
                                               uu____73476;
                                             FStar_Syntax_Syntax.vars =
                                               uu____73477;_}
                                           -> FStar_Syntax_Syntax.bv_eq x y
                                       | uu____73480 -> false  in
                                     if uu____73469
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
                                          let uu____73504 =
                                            let uu____73511 =
                                              let uu____73512 =
                                                let uu____73531 =
                                                  let uu____73540 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____73540]  in
                                                (uu____73531, body1,
                                                  (FStar_Pervasives_Native.Some
                                                     body_rc))
                                                 in
                                              FStar_Syntax_Syntax.Tm_abs
                                                uu____73512
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____73511
                                             in
                                          uu____73504
                                            FStar_Pervasives_Native.None
                                            body1.FStar_Syntax_Syntax.pos
                                           in
                                        let close1 = closure_as_term cfg env
                                           in
                                        let bind_inst =
                                          let uu____73579 =
                                            let uu____73580 =
                                              FStar_Syntax_Subst.compress
                                                bind_repr
                                               in
                                            uu____73580.FStar_Syntax_Syntax.n
                                             in
                                          match uu____73579 with
                                          | FStar_Syntax_Syntax.Tm_uinst
                                              (bind1,uu____73586::uu____73587::[])
                                              ->
                                              let uu____73592 =
                                                let uu____73599 =
                                                  let uu____73600 =
                                                    let uu____73607 =
                                                      let uu____73608 =
                                                        let uu____73609 =
                                                          close1
                                                            lb.FStar_Syntax_Syntax.lbtyp
                                                           in
                                                        (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.FStar_TypeChecker_Cfg.tcenv
                                                          uu____73609
                                                         in
                                                      let uu____73610 =
                                                        let uu____73613 =
                                                          let uu____73614 =
                                                            close1 t  in
                                                          (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                            cfg.FStar_TypeChecker_Cfg.tcenv
                                                            uu____73614
                                                           in
                                                        [uu____73613]  in
                                                      uu____73608 ::
                                                        uu____73610
                                                       in
                                                    (bind1, uu____73607)  in
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                    uu____73600
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____73599
                                                 in
                                              uu____73592
                                                FStar_Pervasives_Native.None
                                                rng
                                          | uu____73617 ->
                                              failwith
                                                "NIY : Reification of indexed effects"
                                           in
                                        let maybe_range_arg =
                                          let uu____73632 =
                                            FStar_Util.for_some
                                              (FStar_Syntax_Util.attr_eq
                                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                                              ed.FStar_Syntax_Syntax.eff_attrs
                                             in
                                          if uu____73632
                                          then
                                            let uu____73645 =
                                              let uu____73654 =
                                                FStar_TypeChecker_Cfg.embed_simple
                                                  FStar_Syntax_Embeddings.e_range
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____73654
                                               in
                                            let uu____73655 =
                                              let uu____73666 =
                                                let uu____73675 =
                                                  FStar_TypeChecker_Cfg.embed_simple
                                                    FStar_Syntax_Embeddings.e_range
                                                    body2.FStar_Syntax_Syntax.pos
                                                    body2.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Syntax_Syntax.as_arg
                                                  uu____73675
                                                 in
                                              [uu____73666]  in
                                            uu____73645 :: uu____73655
                                          else []  in
                                        let reified =
                                          let uu____73713 =
                                            let uu____73720 =
                                              let uu____73721 =
                                                let uu____73738 =
                                                  let uu____73749 =
                                                    let uu____73760 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        lb.FStar_Syntax_Syntax.lbtyp
                                                       in
                                                    let uu____73769 =
                                                      let uu____73780 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          t
                                                         in
                                                      [uu____73780]  in
                                                    uu____73760 ::
                                                      uu____73769
                                                     in
                                                  let uu____73813 =
                                                    let uu____73824 =
                                                      let uu____73835 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          FStar_Syntax_Syntax.tun
                                                         in
                                                      let uu____73844 =
                                                        let uu____73855 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            head4
                                                           in
                                                        let uu____73864 =
                                                          let uu____73875 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          let uu____73884 =
                                                            let uu____73895 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                body2
                                                               in
                                                            [uu____73895]  in
                                                          uu____73875 ::
                                                            uu____73884
                                                           in
                                                        uu____73855 ::
                                                          uu____73864
                                                         in
                                                      uu____73835 ::
                                                        uu____73844
                                                       in
                                                    FStar_List.append
                                                      maybe_range_arg
                                                      uu____73824
                                                     in
                                                  FStar_List.append
                                                    uu____73749 uu____73813
                                                   in
                                                (bind_inst, uu____73738)  in
                                              FStar_Syntax_Syntax.Tm_app
                                                uu____73721
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____73720
                                             in
                                          uu____73713
                                            FStar_Pervasives_Native.None rng
                                           in
                                        FStar_TypeChecker_Cfg.log cfg
                                          (fun uu____73976  ->
                                             let uu____73977 =
                                               FStar_Syntax_Print.term_to_string
                                                 head0
                                                in
                                             let uu____73979 =
                                               FStar_Syntax_Print.term_to_string
                                                 reified
                                                in
                                             FStar_Util.print2
                                               "Reified (1) <%s> to %s\n"
                                               uu____73977 uu____73979);
                                        (let uu____73982 =
                                           FStar_List.tl stack  in
                                         norm cfg env uu____73982 reified)))))
                  | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                      ((let uu____74010 = FStar_Options.defensive ()  in
                        if uu____74010
                        then
                          let is_arg_impure uu____74025 =
                            match uu____74025 with
                            | (e,q) ->
                                let uu____74039 =
                                  let uu____74040 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____74040.FStar_Syntax_Syntax.n  in
                                (match uu____74039 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____74056 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____74056
                                 | uu____74058 -> false)
                             in
                          let uu____74060 =
                            let uu____74062 =
                              let uu____74073 =
                                FStar_Syntax_Syntax.as_arg head_app  in
                              uu____74073 :: args  in
                            FStar_Util.for_some is_arg_impure uu____74062  in
                          (if uu____74060
                           then
                             let uu____74099 =
                               let uu____74105 =
                                 let uu____74107 =
                                   FStar_Syntax_Print.term_to_string head3
                                    in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____74107
                                  in
                               (FStar_Errors.Warning_Defensive, uu____74105)
                                in
                             FStar_Errors.log_issue
                               head3.FStar_Syntax_Syntax.pos uu____74099
                           else ())
                        else ());
                       (let fallback1 uu____74120 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____74124  ->
                               let uu____74125 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____74125 "");
                          (let uu____74129 = FStar_List.tl stack  in
                           let uu____74130 = FStar_Syntax_Util.mk_reify head3
                              in
                           norm cfg env uu____74129 uu____74130)
                           in
                        let fallback2 uu____74136 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____74140  ->
                               let uu____74141 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____74141 "");
                          (let uu____74145 = FStar_List.tl stack  in
                           let uu____74146 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (head3,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               head0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env uu____74145 uu____74146)
                           in
                        let uu____74151 =
                          let uu____74152 =
                            FStar_Syntax_Util.un_uinst head_app  in
                          uu____74152.FStar_Syntax_Syntax.n  in
                        match uu____74151 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____74158 =
                              let uu____74160 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____74160  in
                            if uu____74158
                            then fallback1 ()
                            else
                              (let uu____74165 =
                                 let uu____74167 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____74167  in
                               if uu____74165
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____74184 =
                                      let uu____74189 =
                                        FStar_Syntax_Util.mk_reify head_app
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____74189 args
                                       in
                                    uu____74184 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____74190 = FStar_List.tl stack  in
                                  norm cfg env uu____74190 t1))
                        | uu____74191 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____74193) ->
                      do_reify_monadic fallback cfg env stack e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____74217 = closure_as_term cfg env t'  in
                        reify_lift cfg e msrc mtgt uu____74217  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____74221  ->
                            let uu____74222 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____74222);
                       (let uu____74225 = FStar_List.tl stack  in
                        norm cfg env uu____74225 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                      let branches1 =
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun uu____74346  ->
                                match uu____74346 with
                                | (pat,wopt,tm) ->
                                    let uu____74394 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____74394)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                          head3.FStar_Syntax_Syntax.pos
                         in
                      let uu____74426 = FStar_List.tl stack  in
                      norm cfg env uu____74426 tm
                  | uu____74427 -> fallback ()))

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
              (fun uu____74441  ->
                 let uu____74442 = FStar_Ident.string_of_lid msrc  in
                 let uu____74444 = FStar_Ident.string_of_lid mtgt  in
                 let uu____74446 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____74442
                   uu____74444 uu____74446);
            (let uu____74449 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____74449
             then
               let ed =
                 let uu____74453 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____74453  in
               let uu____74454 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____74454 with
               | (uu____74455,return_repr) ->
                   let return_inst =
                     let uu____74468 =
                       let uu____74469 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____74469.FStar_Syntax_Syntax.n  in
                     match uu____74468 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____74475::[]) ->
                         let uu____74480 =
                           let uu____74487 =
                             let uu____74488 =
                               let uu____74495 =
                                 let uu____74496 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____74496]  in
                               (return_tm, uu____74495)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____74488  in
                           FStar_Syntax_Syntax.mk uu____74487  in
                         uu____74480 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____74499 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____74503 =
                     let uu____74510 =
                       let uu____74511 =
                         let uu____74528 =
                           let uu____74539 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____74548 =
                             let uu____74559 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____74559]  in
                           uu____74539 :: uu____74548  in
                         (return_inst, uu____74528)  in
                       FStar_Syntax_Syntax.Tm_app uu____74511  in
                     FStar_Syntax_Syntax.mk uu____74510  in
                   uu____74503 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____74606 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____74606 with
                | FStar_Pervasives_Native.None  ->
                    let uu____74609 =
                      let uu____74611 = FStar_Ident.text_of_lid msrc  in
                      let uu____74613 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____74611 uu____74613
                       in
                    failwith uu____74609
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____74616;
                      FStar_TypeChecker_Env.mtarget = uu____74617;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____74618;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____74640 =
                      let uu____74642 = FStar_Ident.text_of_lid msrc  in
                      let uu____74644 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____74642 uu____74644
                       in
                    failwith uu____74640
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____74647;
                      FStar_TypeChecker_Env.mtarget = uu____74648;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____74649;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____74684 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____74685 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____74684 t FStar_Syntax_Syntax.tun uu____74685))

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
                (fun uu____74755  ->
                   match uu____74755 with
                   | (a,imp) ->
                       let uu____74774 = norm cfg env [] a  in
                       (uu____74774, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____74784  ->
             let uu____74785 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____74787 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____74785 uu____74787);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____74813 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _74816  -> FStar_Pervasives_Native.Some _74816)
                     uu____74813
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2599_74817 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2599_74817.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2599_74817.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____74839 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _74842  -> FStar_Pervasives_Native.Some _74842)
                     uu____74839
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2610_74843 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2610_74843.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2610_74843.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____74888  ->
                      match uu____74888 with
                      | (a,i) ->
                          let uu____74908 = norm cfg env [] a  in
                          (uu____74908, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___600_74930  ->
                       match uu___600_74930 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____74934 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____74934
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___2627_74942 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2629_74945 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2629_74945.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2627_74942.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2627_74942.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun b  ->
        let uu____74949 = b  in
        match uu____74949 with
        | (x,imp) ->
            let x1 =
              let uu___2637_74957 = x  in
              let uu____74958 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2637_74957.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2637_74957.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____74958
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____74969 =
                    let uu____74970 = closure_as_term cfg env t  in
                    FStar_Syntax_Syntax.Meta uu____74970  in
                  FStar_Pervasives_Native.Some uu____74969
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____74981 =
          FStar_List.fold_left
            (fun uu____75015  ->
               fun b  ->
                 match uu____75015 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____74981 with | (nbs,uu____75095) -> FStar_List.rev nbs

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
            let uu____75127 =
              let uu___2662_75128 = rc  in
              let uu____75129 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2662_75128.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____75129;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2662_75128.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____75127
        | uu____75138 -> lopt

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
            (let uu____75148 = FStar_Syntax_Print.term_to_string tm  in
             let uu____75150 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____75148 uu____75150)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___601_75162  ->
      match uu___601_75162 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____75175 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____75175 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____75179 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____75179)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____75187 = norm_cb cfg  in
            reduce_primops uu____75187 cfg env tm  in
          let uu____75192 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____75192
          then tm1
          else
            (let w t =
               let uu___2690_75211 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2690_75211.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2690_75211.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____75223 =
                 let uu____75224 = FStar_Syntax_Util.unmeta t  in
                 uu____75224.FStar_Syntax_Syntax.n  in
               match uu____75223 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____75236 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____75300)::args1,(bv,uu____75303)::bs1) ->
                   let uu____75357 =
                     let uu____75358 = FStar_Syntax_Subst.compress t  in
                     uu____75358.FStar_Syntax_Syntax.n  in
                   (match uu____75357 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____75363 -> false)
               | ([],[]) -> true
               | (uu____75394,uu____75395) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____75446 = FStar_Syntax_Print.term_to_string t  in
                  let uu____75448 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____75446
                    uu____75448)
               else ();
               (let uu____75453 = FStar_Syntax_Util.head_and_args' t  in
                match uu____75453 with
                | (hd1,args) ->
                    let uu____75492 =
                      let uu____75493 = FStar_Syntax_Subst.compress hd1  in
                      uu____75493.FStar_Syntax_Syntax.n  in
                    (match uu____75492 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____75501 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____75503 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____75505 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____75501 uu____75503 uu____75505)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____75510 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____75528 = FStar_Syntax_Print.term_to_string t  in
                  let uu____75530 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____75528
                    uu____75530)
               else ();
               (let uu____75535 = FStar_Syntax_Util.is_squash t  in
                match uu____75535 with
                | FStar_Pervasives_Native.Some (uu____75546,t') ->
                    is_applied bs t'
                | uu____75558 ->
                    let uu____75567 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____75567 with
                     | FStar_Pervasives_Native.Some (uu____75578,t') ->
                         is_applied bs t'
                     | uu____75590 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____75614 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____75614 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____75621)::(q,uu____75623)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____75666 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____75668 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____75666 uu____75668)
                    else ();
                    (let uu____75673 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____75673 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____75678 =
                           let uu____75679 = FStar_Syntax_Subst.compress p
                              in
                           uu____75679.FStar_Syntax_Syntax.n  in
                         (match uu____75678 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____75690 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____75690))
                          | uu____75693 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____75696)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____75721 =
                           let uu____75722 = FStar_Syntax_Subst.compress p1
                              in
                           uu____75722.FStar_Syntax_Syntax.n  in
                         (match uu____75721 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____75733 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____75733))
                          | uu____75736 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____75740 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____75740 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____75745 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____75745 with
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
                                     let uu____75759 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____75759))
                               | uu____75762 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____75767)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____75792 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____75792 with
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
                                     let uu____75806 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____75806))
                               | uu____75809 -> FStar_Pervasives_Native.None)
                          | uu____75812 -> FStar_Pervasives_Native.None)
                     | uu____75815 -> FStar_Pervasives_Native.None))
               | uu____75818 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____75831 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____75831 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____75837)::[],uu____75838,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____75858 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____75860 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____75858
                         uu____75860)
                    else ();
                    is_quantified_const bv phi')
               | uu____75865 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____75880 =
                 let uu____75881 = FStar_Syntax_Subst.compress phi  in
                 uu____75881.FStar_Syntax_Syntax.n  in
               match uu____75880 with
               | FStar_Syntax_Syntax.Tm_match (uu____75887,br::brs) ->
                   let uu____75954 = br  in
                   (match uu____75954 with
                    | (uu____75972,uu____75973,e) ->
                        let r =
                          let uu____75995 = simp_t e  in
                          match uu____75995 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____76007 =
                                FStar_List.for_all
                                  (fun uu____76026  ->
                                     match uu____76026 with
                                     | (uu____76040,uu____76041,e') ->
                                         let uu____76055 = simp_t e'  in
                                         uu____76055 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____76007
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____76071 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____76081 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____76081
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____76119 =
                 match uu____76119 with
                 | (t1,q) ->
                     let uu____76140 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____76140 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____76172 -> (t1, q))
                  in
               let uu____76185 = FStar_Syntax_Util.head_and_args t  in
               match uu____76185 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____76265 =
                 let uu____76266 = FStar_Syntax_Util.unmeta ty  in
                 uu____76266.FStar_Syntax_Syntax.n  in
               match uu____76265 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____76271) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____76276,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____76300 -> false  in
             let simplify1 arg =
               let uu____76333 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____76333, arg)  in
             let uu____76348 = is_forall_const tm1  in
             match uu____76348 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____76354 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____76356 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____76354
                       uu____76356)
                  else ();
                  (let uu____76361 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____76361))
             | FStar_Pervasives_Native.None  ->
                 let uu____76362 =
                   let uu____76363 = FStar_Syntax_Subst.compress tm1  in
                   uu____76363.FStar_Syntax_Syntax.n  in
                 (match uu____76362 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____76367;
                              FStar_Syntax_Syntax.vars = uu____76368;_},uu____76369);
                         FStar_Syntax_Syntax.pos = uu____76370;
                         FStar_Syntax_Syntax.vars = uu____76371;_},args)
                      ->
                      let uu____76401 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____76401
                      then
                        let uu____76404 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____76404 with
                         | (FStar_Pervasives_Native.Some (true ),uu____76462)::
                             (uu____76463,(arg,uu____76465))::[] ->
                             maybe_auto_squash arg
                         | (uu____76538,(arg,uu____76540))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____76541)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____76614)::uu____76615::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____76685::(FStar_Pervasives_Native.Some (false
                                         ),uu____76686)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____76756 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____76774 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____76774
                         then
                           let uu____76777 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____76777 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____76835)::uu____76836::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____76906::(FStar_Pervasives_Native.Some (true
                                           ),uu____76907)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____76977)::(uu____76978,(arg,uu____76980))::[]
                               -> maybe_auto_squash arg
                           | (uu____77053,(arg,uu____77055))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____77056)::[]
                               -> maybe_auto_squash arg
                           | uu____77129 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____77147 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____77147
                            then
                              let uu____77150 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____77150 with
                              | uu____77208::(FStar_Pervasives_Native.Some
                                              (true ),uu____77209)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____77279)::uu____77280::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____77350)::(uu____77351,(arg,uu____77353))::[]
                                  -> maybe_auto_squash arg
                              | (uu____77426,(p,uu____77428))::(uu____77429,
                                                                (q,uu____77431))::[]
                                  ->
                                  let uu____77503 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____77503
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____77508 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____77526 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____77526
                               then
                                 let uu____77529 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____77529 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____77587)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____77588)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____77662)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____77663)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____77737)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____77738)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____77812)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____77813)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____77887,(arg,uu____77889))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____77890)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____77963)::(uu____77964,(arg,uu____77966))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____78039,(arg,uu____78041))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____78042)::[]
                                     ->
                                     let uu____78115 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____78115
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____78116)::(uu____78117,(arg,uu____78119))::[]
                                     ->
                                     let uu____78192 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____78192
                                 | (uu____78193,(p,uu____78195))::(uu____78196,
                                                                   (q,uu____78198))::[]
                                     ->
                                     let uu____78270 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____78270
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____78275 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____78293 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____78293
                                  then
                                    let uu____78296 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____78296 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____78354)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____78398)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____78442 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____78460 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____78460
                                     then
                                       match args with
                                       | (t,uu____78464)::[] ->
                                           let uu____78489 =
                                             let uu____78490 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____78490.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____78489 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____78493::[],body,uu____78495)
                                                ->
                                                let uu____78530 = simp_t body
                                                   in
                                                (match uu____78530 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____78536 -> tm1)
                                            | uu____78540 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____78542))::(t,uu____78544)::[]
                                           ->
                                           let uu____78584 =
                                             let uu____78585 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____78585.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____78584 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____78588::[],body,uu____78590)
                                                ->
                                                let uu____78625 = simp_t body
                                                   in
                                                (match uu____78625 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____78633 -> tm1)
                                            | uu____78637 -> tm1)
                                       | uu____78638 -> tm1
                                     else
                                       (let uu____78651 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____78651
                                        then
                                          match args with
                                          | (t,uu____78655)::[] ->
                                              let uu____78680 =
                                                let uu____78681 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____78681.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____78680 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____78684::[],body,uu____78686)
                                                   ->
                                                   let uu____78721 =
                                                     simp_t body  in
                                                   (match uu____78721 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____78727 -> tm1)
                                               | uu____78731 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____78733))::(t,uu____78735)::[]
                                              ->
                                              let uu____78775 =
                                                let uu____78776 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____78776.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____78775 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____78779::[],body,uu____78781)
                                                   ->
                                                   let uu____78816 =
                                                     simp_t body  in
                                                   (match uu____78816 with
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
                                                    | uu____78824 -> tm1)
                                               | uu____78828 -> tm1)
                                          | uu____78829 -> tm1
                                        else
                                          (let uu____78842 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____78842
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____78845;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____78846;_},uu____78847)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____78873;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____78874;_},uu____78875)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____78901 -> tm1
                                           else
                                             (let uu____78914 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____78914
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____78928 =
                                                    let uu____78929 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____78929.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____78928 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____78940 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     (Prims.parse_int "1")
                                                 then
                                                   let t =
                                                     let uu____78954 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____78954
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____78993 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____78993
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____78999 =
                                                         let uu____79000 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____79000.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____78999 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____79003 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____79011 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____79011
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____79020
                                                                  =
                                                                  let uu____79021
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____79021.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____79020
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____79027)
                                                                    -> hd1
                                                                | uu____79052
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____79056
                                                                =
                                                                let uu____79067
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____79067]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____79056)
                                                       | uu____79100 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____79105 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____79105 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____79125 ->
                                                     let uu____79134 =
                                                       let uu____79141 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____79141 cfg env
                                                        in
                                                     uu____79134 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____79147;
                         FStar_Syntax_Syntax.vars = uu____79148;_},args)
                      ->
                      let uu____79174 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____79174
                      then
                        let uu____79177 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____79177 with
                         | (FStar_Pervasives_Native.Some (true ),uu____79235)::
                             (uu____79236,(arg,uu____79238))::[] ->
                             maybe_auto_squash arg
                         | (uu____79311,(arg,uu____79313))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____79314)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____79387)::uu____79388::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____79458::(FStar_Pervasives_Native.Some (false
                                         ),uu____79459)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____79529 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____79547 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____79547
                         then
                           let uu____79550 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____79550 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____79608)::uu____79609::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____79679::(FStar_Pervasives_Native.Some (true
                                           ),uu____79680)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____79750)::(uu____79751,(arg,uu____79753))::[]
                               -> maybe_auto_squash arg
                           | (uu____79826,(arg,uu____79828))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____79829)::[]
                               -> maybe_auto_squash arg
                           | uu____79902 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____79920 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____79920
                            then
                              let uu____79923 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____79923 with
                              | uu____79981::(FStar_Pervasives_Native.Some
                                              (true ),uu____79982)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____80052)::uu____80053::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____80123)::(uu____80124,(arg,uu____80126))::[]
                                  -> maybe_auto_squash arg
                              | (uu____80199,(p,uu____80201))::(uu____80202,
                                                                (q,uu____80204))::[]
                                  ->
                                  let uu____80276 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____80276
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____80281 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____80299 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____80299
                               then
                                 let uu____80302 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____80302 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____80360)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____80361)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____80435)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____80436)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____80510)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____80511)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____80585)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____80586)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____80660,(arg,uu____80662))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____80663)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____80736)::(uu____80737,(arg,uu____80739))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____80812,(arg,uu____80814))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____80815)::[]
                                     ->
                                     let uu____80888 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____80888
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____80889)::(uu____80890,(arg,uu____80892))::[]
                                     ->
                                     let uu____80965 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____80965
                                 | (uu____80966,(p,uu____80968))::(uu____80969,
                                                                   (q,uu____80971))::[]
                                     ->
                                     let uu____81043 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____81043
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____81048 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____81066 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____81066
                                  then
                                    let uu____81069 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____81069 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____81127)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____81171)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____81215 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____81233 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____81233
                                     then
                                       match args with
                                       | (t,uu____81237)::[] ->
                                           let uu____81262 =
                                             let uu____81263 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____81263.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____81262 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____81266::[],body,uu____81268)
                                                ->
                                                let uu____81303 = simp_t body
                                                   in
                                                (match uu____81303 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____81309 -> tm1)
                                            | uu____81313 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____81315))::(t,uu____81317)::[]
                                           ->
                                           let uu____81357 =
                                             let uu____81358 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____81358.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____81357 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____81361::[],body,uu____81363)
                                                ->
                                                let uu____81398 = simp_t body
                                                   in
                                                (match uu____81398 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____81406 -> tm1)
                                            | uu____81410 -> tm1)
                                       | uu____81411 -> tm1
                                     else
                                       (let uu____81424 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____81424
                                        then
                                          match args with
                                          | (t,uu____81428)::[] ->
                                              let uu____81453 =
                                                let uu____81454 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____81454.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____81453 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____81457::[],body,uu____81459)
                                                   ->
                                                   let uu____81494 =
                                                     simp_t body  in
                                                   (match uu____81494 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____81500 -> tm1)
                                               | uu____81504 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____81506))::(t,uu____81508)::[]
                                              ->
                                              let uu____81548 =
                                                let uu____81549 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____81549.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____81548 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____81552::[],body,uu____81554)
                                                   ->
                                                   let uu____81589 =
                                                     simp_t body  in
                                                   (match uu____81589 with
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
                                                    | uu____81597 -> tm1)
                                               | uu____81601 -> tm1)
                                          | uu____81602 -> tm1
                                        else
                                          (let uu____81615 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____81615
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____81618;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____81619;_},uu____81620)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____81646;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____81647;_},uu____81648)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____81674 -> tm1
                                           else
                                             (let uu____81687 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____81687
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____81701 =
                                                    let uu____81702 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____81702.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____81701 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____81713 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     (Prims.parse_int "1")
                                                 then
                                                   let t =
                                                     let uu____81727 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____81727
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____81762 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____81762
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____81768 =
                                                         let uu____81769 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____81769.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____81768 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____81772 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____81780 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____81780
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____81789
                                                                  =
                                                                  let uu____81790
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____81790.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____81789
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____81796)
                                                                    -> hd1
                                                                | uu____81821
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____81825
                                                                =
                                                                let uu____81836
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____81836]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____81825)
                                                       | uu____81869 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____81874 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____81874 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____81894 ->
                                                     let uu____81903 =
                                                       let uu____81910 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____81910 cfg env
                                                        in
                                                     uu____81903 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____81921 = simp_t t  in
                      (match uu____81921 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____81930 ->
                      let uu____81953 = is_const_match tm1  in
                      (match uu____81953 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____81962 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____81972  ->
               (let uu____81974 = FStar_Syntax_Print.tag_of_term t  in
                let uu____81976 = FStar_Syntax_Print.term_to_string t  in
                let uu____81978 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____81986 =
                  let uu____81988 =
                    let uu____81991 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____81991
                     in
                  stack_to_string uu____81988  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____81974 uu____81976 uu____81978 uu____81986);
               (let uu____82016 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____82016
                then
                  let uu____82020 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____82020 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____82027 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____82029 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____82031 =
                          let uu____82033 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____82033
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____82027
                          uu____82029 uu____82031);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____82055 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack with
                | (Arg uu____82063)::uu____82064 -> true
                | uu____82074 -> false)
              in
           if uu____82055
           then
             let uu____82077 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____82077 (norm cfg env stack)
           else
             (let t1 = maybe_simplify cfg env stack t  in
              match stack with
              | [] -> t1
              | (Debug (tm,time_then))::stack1 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now ()  in
                      let uu____82091 =
                        let uu____82093 =
                          let uu____82095 =
                            FStar_Util.time_diff time_then time_now  in
                          FStar_Pervasives_Native.snd uu____82095  in
                        FStar_Util.string_of_int uu____82093  in
                      let uu____82102 = FStar_Syntax_Print.term_to_string tm
                         in
                      let uu____82104 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print3
                        "Normalized term (%s ms) %s\n\tto term %s\n"
                        uu____82091 uu____82102 uu____82104)
                   else ();
                   rebuild cfg env stack1 t1)
              | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
              | (Meta (uu____82113,m,r))::stack1 ->
                  let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
                  rebuild cfg env stack1 t2
              | (MemoLazy r)::stack1 ->
                  (set_memo cfg r (env, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu____82142  ->
                        let uu____82143 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 "\tSet memo %s\n" uu____82143);
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
                  let uu____82186 =
                    let uu___3319_82187 = FStar_Syntax_Util.abs bs1 t1 lopt1
                       in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___3319_82187.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___3319_82187.FStar_Syntax_Syntax.vars)
                    }  in
                  rebuild cfg env stack1 uu____82186
              | (Arg (Univ uu____82190,uu____82191,uu____82192))::uu____82193
                  -> failwith "Impossible"
              | (Arg (Dummy ,uu____82197,uu____82198))::uu____82199 ->
                  failwith "Impossible"
              | (UnivArgs (us,r))::stack1 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                  rebuild cfg env stack1 t2
              | (Arg
                  (Clos (env_arg,tm,uu____82215,uu____82216),aq,r))::stack1
                  when
                  let uu____82268 = head_of t1  in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____82268 ->
                  let t2 =
                    let uu____82272 =
                      let uu____82277 =
                        let uu____82278 = closure_as_term cfg env_arg tm  in
                        (uu____82278, aq)  in
                      FStar_Syntax_Syntax.extend_app t1 uu____82277  in
                    uu____82272 FStar_Pervasives_Native.None r  in
                  rebuild cfg env stack1 t2
              | (Arg (Clos (env_arg,tm,m,uu____82288),aq,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____82343  ->
                        let uu____82344 =
                          FStar_Syntax_Print.term_to_string tm  in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____82344);
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
                     (let uu____82364 = FStar_ST.op_Bang m  in
                      match uu____82364 with
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
                      | FStar_Pervasives_Native.Some (uu____82452,a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq)
                              FStar_Pervasives_Native.None r
                             in
                          rebuild cfg env_arg stack1 t2))
              | (App (env1,head1,aq,r))::stack' when should_reify cfg stack
                  ->
                  let t0 = t1  in
                  let fallback msg uu____82508 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____82513  ->
                         let uu____82514 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____82514);
                    (let t2 =
                       FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env1 stack' t2)
                     in
                  let uu____82524 =
                    let uu____82525 = FStar_Syntax_Subst.compress t1  in
                    uu____82525.FStar_Syntax_Syntax.n  in
                  (match uu____82524 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env1 stack t2 m
                         ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc,mtgt,ty))
                       ->
                       let lifted =
                         let uu____82553 = closure_as_term cfg env1 ty  in
                         reify_lift cfg t2 msrc mtgt uu____82553  in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____82557  ->
                             let uu____82558 =
                               FStar_Syntax_Print.term_to_string lifted  in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____82558);
                        (let uu____82561 = FStar_List.tl stack  in
                         norm cfg env1 uu____82561 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu____82562);
                          FStar_Syntax_Syntax.pos = uu____82563;
                          FStar_Syntax_Syntax.vars = uu____82564;_},(e,uu____82566)::[])
                       -> norm cfg env1 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____82605 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____82622 = FStar_Syntax_Util.head_and_args t1
                          in
                       (match uu____82622 with
                        | (hd1,args) ->
                            let uu____82665 =
                              let uu____82666 =
                                FStar_Syntax_Util.un_uinst hd1  in
                              uu____82666.FStar_Syntax_Syntax.n  in
                            (match uu____82665 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____82670 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv
                                    in
                                 (match uu____82670 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____82673;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____82674;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____82675;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n1;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____82677;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____82678;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____82679;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____82680;_}
                                      when (FStar_List.length args) = n1 ->
                                      norm cfg env1 stack' t1
                                  | uu____82716 -> fallback " (3)" ())
                             | uu____82720 -> fallback " (4)" ()))
                   | uu____82722 -> fallback " (2)" ())
              | (App (env1,head1,aq,r))::stack1 ->
                  let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack1 t2
              | (Match (env',branches,cfg1,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____82748  ->
                        let uu____82749 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____82749);
                   (let scrutinee_env = env  in
                    let env1 = env'  in
                    let scrutinee = t1  in
                    let norm_and_rebuild_match uu____82760 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____82765  ->
                           let uu____82766 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           let uu____82768 =
                             let uu____82770 =
                               FStar_All.pipe_right branches
                                 (FStar_List.map
                                    (fun uu____82800  ->
                                       match uu____82800 with
                                       | (p,uu____82811,uu____82812) ->
                                           FStar_Syntax_Print.pat_to_string p))
                                in
                             FStar_All.pipe_right uu____82770
                               (FStar_String.concat "\n\t")
                              in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu____82766 uu____82768);
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
                                (fun uu___602_82834  ->
                                   match uu___602_82834 with
                                   | FStar_TypeChecker_Env.InliningDelta  ->
                                       true
                                   | FStar_TypeChecker_Env.Eager_unfolding_only
                                        -> true
                                   | uu____82838 -> false))
                            in
                         let steps =
                           let uu___3487_82841 =
                             cfg1.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___3487_82841.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___3487_82841.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta = false;
                             FStar_TypeChecker_Cfg.weak =
                               (uu___3487_82841.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___3487_82841.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___3487_82841.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___3487_82841.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_only =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___3487_82841.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_tac = false;
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___3487_82841.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___3487_82841.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___3487_82841.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___3487_82841.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___3487_82841.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___3487_82841.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___3487_82841.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___3487_82841.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___3487_82841.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___3487_82841.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___3487_82841.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___3487_82841.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___3487_82841.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___3487_82841.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         let uu___3490_82848 = cfg1  in
                         {
                           FStar_TypeChecker_Cfg.steps = steps;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___3490_82848.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___3490_82848.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = new_delta;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___3490_82848.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong = true;
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___3490_82848.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets =
                             (uu___3490_82848.FStar_TypeChecker_Cfg.normalize_pure_lets);
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___3490_82848.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let norm_or_whnf env2 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env2 t2
                         else norm cfg_exclude_zeta env2 [] t2  in
                       let rec norm_pat env2 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu____82923 ->
                             (p, env2)
                         | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                             let uu____82954 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____83043  ->
                                       fun uu____83044  ->
                                         match (uu____83043, uu____83044)
                                         with
                                         | ((pats1,env3),(p1,b)) ->
                                             let uu____83194 =
                                               norm_pat env3 p1  in
                                             (match uu____83194 with
                                              | (p2,env4) ->
                                                  (((p2, b) :: pats1), env4)))
                                    ([], env2))
                                in
                             (match uu____82954 with
                              | (pats1,env3) ->
                                  ((let uu___3518_83364 = p  in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___3518_83364.FStar_Syntax_Syntax.p)
                                    }), env3))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___3522_83385 = x  in
                               let uu____83386 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3522_83385.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3522_83385.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____83386
                               }  in
                             ((let uu___3525_83400 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3525_83400.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___3529_83411 = x  in
                               let uu____83412 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3529_83411.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3529_83411.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____83412
                               }  in
                             ((let uu___3532_83426 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3532_83426.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                             let x1 =
                               let uu___3538_83442 = x  in
                               let uu____83443 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3538_83442.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3538_83442.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____83443
                               }  in
                             let t3 = norm_or_whnf env2 t2  in
                             ((let uu___3542_83458 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___3542_83458.FStar_Syntax_Syntax.p)
                               }), env2)
                          in
                       let branches1 =
                         match env1 with
                         | [] when whnf -> branches
                         | uu____83502 ->
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun branch1  ->
                                     let uu____83532 =
                                       FStar_Syntax_Subst.open_branch branch1
                                        in
                                     match uu____83532 with
                                     | (p,wopt,e) ->
                                         let uu____83552 = norm_pat env1 p
                                            in
                                         (match uu____83552 with
                                          | (p1,env2) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu____83607 =
                                                      norm_or_whnf env2 w  in
                                                    FStar_Pervasives_Native.Some
                                                      uu____83607
                                                 in
                                              let e1 = norm_or_whnf env2 e
                                                 in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1))))
                          in
                       let scrutinee1 =
                         let uu____83624 =
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
                         if uu____83624
                         then
                           norm
                             (let uu___3561_83631 = cfg1  in
                              {
                                FStar_TypeChecker_Cfg.steps =
                                  (let uu___3563_83634 =
                                     cfg1.FStar_TypeChecker_Cfg.steps  in
                                   {
                                     FStar_TypeChecker_Cfg.beta =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.beta);
                                     FStar_TypeChecker_Cfg.iota =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.iota);
                                     FStar_TypeChecker_Cfg.zeta =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.zeta);
                                     FStar_TypeChecker_Cfg.weak =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.weak);
                                     FStar_TypeChecker_Cfg.hnf =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.hnf);
                                     FStar_TypeChecker_Cfg.primops =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.primops);
                                     FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                       =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                     FStar_TypeChecker_Cfg.unfold_until =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.unfold_until);
                                     FStar_TypeChecker_Cfg.unfold_only =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.unfold_only);
                                     FStar_TypeChecker_Cfg.unfold_fully =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.unfold_fully);
                                     FStar_TypeChecker_Cfg.unfold_attr =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.unfold_attr);
                                     FStar_TypeChecker_Cfg.unfold_tac =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.unfold_tac);
                                     FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                       =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                     FStar_TypeChecker_Cfg.simplify =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.simplify);
                                     FStar_TypeChecker_Cfg.erase_universes =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.erase_universes);
                                     FStar_TypeChecker_Cfg.allow_unbound_universes
                                       =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                     FStar_TypeChecker_Cfg.reify_ =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.reify_);
                                     FStar_TypeChecker_Cfg.compress_uvars =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.compress_uvars);
                                     FStar_TypeChecker_Cfg.no_full_norm =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.no_full_norm);
                                     FStar_TypeChecker_Cfg.check_no_uvars =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.check_no_uvars);
                                     FStar_TypeChecker_Cfg.unmeta =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.unmeta);
                                     FStar_TypeChecker_Cfg.unascribe =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.unascribe);
                                     FStar_TypeChecker_Cfg.in_full_norm_request
                                       =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.in_full_norm_request);
                                     FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                       = false;
                                     FStar_TypeChecker_Cfg.nbe_step =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.nbe_step);
                                     FStar_TypeChecker_Cfg.for_extraction =
                                       (uu___3563_83634.FStar_TypeChecker_Cfg.for_extraction)
                                   });
                                FStar_TypeChecker_Cfg.tcenv =
                                  (uu___3561_83631.FStar_TypeChecker_Cfg.tcenv);
                                FStar_TypeChecker_Cfg.debug =
                                  (uu___3561_83631.FStar_TypeChecker_Cfg.debug);
                                FStar_TypeChecker_Cfg.delta_level =
                                  (uu___3561_83631.FStar_TypeChecker_Cfg.delta_level);
                                FStar_TypeChecker_Cfg.primitive_steps =
                                  (uu___3561_83631.FStar_TypeChecker_Cfg.primitive_steps);
                                FStar_TypeChecker_Cfg.strong =
                                  (uu___3561_83631.FStar_TypeChecker_Cfg.strong);
                                FStar_TypeChecker_Cfg.memoize_lazy =
                                  (uu___3561_83631.FStar_TypeChecker_Cfg.memoize_lazy);
                                FStar_TypeChecker_Cfg.normalize_pure_lets =
                                  (uu___3561_83631.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                FStar_TypeChecker_Cfg.reifying =
                                  (uu___3561_83631.FStar_TypeChecker_Cfg.reifying)
                              }) scrutinee_env [] scrutinee
                         else scrutinee  in
                       let uu____83638 =
                         mk
                           (FStar_Syntax_Syntax.Tm_match
                              (scrutinee1, branches1)) r
                          in
                       rebuild cfg1 env1 stack1 uu____83638)
                       in
                    let rec is_cons head1 =
                      let uu____83664 =
                        let uu____83665 = FStar_Syntax_Subst.compress head1
                           in
                        uu____83665.FStar_Syntax_Syntax.n  in
                      match uu____83664 with
                      | FStar_Syntax_Syntax.Tm_uinst (h,uu____83670) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____83675 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____83677;
                            FStar_Syntax_Syntax.fv_delta = uu____83678;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor );_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____83680;
                            FStar_Syntax_Syntax.fv_delta = uu____83681;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____83682);_}
                          -> true
                      | uu____83690 -> false  in
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
                      let uu____83859 =
                        FStar_Syntax_Util.head_and_args scrutinee2  in
                      match uu____83859 with
                      | (head1,args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu____83956 ->
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
                                | uu____83998 ->
                                    let uu____83999 =
                                      let uu____84001 = is_cons head1  in
                                      Prims.op_Negation uu____84001  in
                                    FStar_Util.Inr uu____83999)
                           | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                               let uu____84030 =
                                 let uu____84031 =
                                   FStar_Syntax_Util.un_uinst head1  in
                                 uu____84031.FStar_Syntax_Syntax.n  in
                               (match uu____84030 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____84050 ->
                                    let uu____84051 =
                                      let uu____84053 = is_cons head1  in
                                      Prims.op_Negation uu____84053  in
                                    FStar_Util.Inr uu____84051))
                    
                    and matches_args out a p =
                      match (a, p) with
                      | ([],[]) -> FStar_Util.Inl out
                      | ((t2,uu____84144)::rest_a,(p1,uu____84147)::rest_p)
                          ->
                          let uu____84206 = matches_pat t2 p1  in
                          (match uu____84206 with
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu____84259 -> FStar_Util.Inr false
                     in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1,wopt,b)::rest ->
                          let uu____84382 = matches_pat scrutinee1 p1  in
                          (match uu____84382 with
                           | FStar_Util.Inr (false ) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true ) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu____84428  ->
                                     let uu____84429 =
                                       FStar_Syntax_Print.pat_to_string p1
                                        in
                                     let uu____84431 =
                                       let uu____84433 =
                                         FStar_List.map
                                           (fun uu____84445  ->
                                              match uu____84445 with
                                              | (uu____84451,t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s
                                          in
                                       FStar_All.pipe_right uu____84433
                                         (FStar_String.concat "; ")
                                        in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu____84429 uu____84431);
                                (let env0 = env1  in
                                 let env2 =
                                   FStar_List.fold_left
                                     (fun env2  ->
                                        fun uu____84487  ->
                                          match uu____84487 with
                                          | (bv,t2) ->
                                              let uu____84510 =
                                                let uu____84517 =
                                                  let uu____84520 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____84520
                                                   in
                                                let uu____84521 =
                                                  let uu____84522 =
                                                    let uu____84554 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2))
                                                       in
                                                    ([], t2, uu____84554,
                                                      false)
                                                     in
                                                  Clos uu____84522  in
                                                (uu____84517, uu____84521)
                                                 in
                                              uu____84510 :: env2) env1 s
                                    in
                                 let uu____84647 =
                                   guard_when_clause wopt b rest  in
                                 norm cfg1 env2 stack1 uu____84647)))
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
            (fun uu____84680  ->
               let uu____84681 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____84681);
          (let uu____84684 = is_nbe_request s  in
           if uu____84684
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____84690  ->
                   let uu____84691 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____84691);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____84697  ->
                   let uu____84698 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____84698);
              (let uu____84701 =
                 FStar_Util.record_time (fun uu____84708  -> nbe_eval c s t)
                  in
               match uu____84701 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____84717  ->
                         let uu____84718 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____84720 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____84718 uu____84720);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____84728  ->
                   let uu____84729 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____84729);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____84735  ->
                   let uu____84736 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____84736);
              (let uu____84739 =
                 FStar_Util.record_time (fun uu____84746  -> norm c [] [] t)
                  in
               match uu____84739 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____84761  ->
                         let uu____84762 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____84764 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____84762 uu____84764);
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
        let uu____84799 = FStar_TypeChecker_Cfg.config s e  in
        norm_comp uu____84799 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____84817 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____84817 [] u
  
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
        let uu____84843 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____84843  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____84850 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___3719_84869 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3719_84869.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3719_84869.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name
              cfg.FStar_TypeChecker_Cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____84876 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____84876
          then
            let ct1 =
              let uu____84880 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____84880 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____84887 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____84887
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3729_84894 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3729_84894.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3729_84894.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3729_84894.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev
                      cfg.FStar_TypeChecker_Cfg.tcenv c
                     in
                  let uu___3733_84896 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3733_84896.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3733_84896.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3733_84896.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3733_84896.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3736_84897 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3736_84897.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3736_84897.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____84900 -> c
  
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
        let uu____84920 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____84920  in
      let uu____84927 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____84927
      then
        let uu____84930 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____84930 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____84936  ->
                 let uu____84937 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____84937)
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
          (fun uu___3752_84954  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___3751_84957 ->
            ((let uu____84959 =
                let uu____84965 =
                  let uu____84967 = FStar_Util.message_of_exn uu___3751_84957
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____84967
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____84965)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____84959);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          (fun uu___3762_84986  ->
             match () with
             | () ->
                 let uu____84987 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____84987 [] c) ()
        with
        | uu___3761_84996 ->
            ((let uu____84998 =
                let uu____85004 =
                  let uu____85006 = FStar_Util.message_of_exn uu___3761_84996
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____85006
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____85004)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____84998);
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
                   let uu____85055 =
                     let uu____85056 =
                       let uu____85063 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____85063)  in
                     FStar_Syntax_Syntax.Tm_refine uu____85056  in
                   mk uu____85055 t01.FStar_Syntax_Syntax.pos
               | uu____85068 -> t2)
          | uu____85069 -> t2  in
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
        let uu____85163 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____85163 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____85200 ->
                 let uu____85209 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____85209 with
                  | (actuals,uu____85219,uu____85220) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____85240 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____85240 with
                         | (binders,args) ->
                             let uu____85251 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____85251
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
      | uu____85266 ->
          let uu____85267 = FStar_Syntax_Util.head_and_args t  in
          (match uu____85267 with
           | (head1,args) ->
               let uu____85310 =
                 let uu____85311 = FStar_Syntax_Subst.compress head1  in
                 uu____85311.FStar_Syntax_Syntax.n  in
               (match uu____85310 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____85332 =
                      let uu____85347 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____85347  in
                    (match uu____85332 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____85387 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___3832_85395 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3832_85395.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3832_85395.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3832_85395.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3832_85395.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3832_85395.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3832_85395.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3832_85395.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3832_85395.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3832_85395.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___3832_85395.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3832_85395.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3832_85395.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3832_85395.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3832_85395.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3832_85395.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3832_85395.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3832_85395.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3832_85395.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3832_85395.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3832_85395.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3832_85395.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3832_85395.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3832_85395.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3832_85395.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3832_85395.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3832_85395.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3832_85395.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3832_85395.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3832_85395.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3832_85395.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3832_85395.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3832_85395.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3832_85395.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3832_85395.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3832_85395.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___3832_85395.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3832_85395.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3832_85395.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3832_85395.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3832_85395.FStar_TypeChecker_Env.nbe)
                                 }) t
                               in
                            match uu____85387 with
                            | (uu____85398,ty,uu____85400) ->
                                eta_expand_with_type env t ty))
                | uu____85401 ->
                    let uu____85402 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___3839_85410 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3839_85410.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3839_85410.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3839_85410.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3839_85410.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3839_85410.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3839_85410.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3839_85410.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3839_85410.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3839_85410.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___3839_85410.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3839_85410.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3839_85410.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3839_85410.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3839_85410.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3839_85410.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3839_85410.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3839_85410.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3839_85410.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3839_85410.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3839_85410.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3839_85410.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3839_85410.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3839_85410.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3839_85410.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3839_85410.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3839_85410.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3839_85410.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3839_85410.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3839_85410.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3839_85410.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3839_85410.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3839_85410.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3839_85410.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3839_85410.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3839_85410.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___3839_85410.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3839_85410.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3839_85410.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3839_85410.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3839_85410.FStar_TypeChecker_Env.nbe)
                         }) t
                       in
                    (match uu____85402 with
                     | (uu____85413,ty,uu____85415) ->
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
      let uu___3851_85497 = x  in
      let uu____85498 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3851_85497.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3851_85497.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____85498
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____85501 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____85525 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____85526 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____85527 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____85528 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____85535 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____85536 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____85537 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3877_85571 = rc  in
          let uu____85572 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____85581 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3877_85571.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____85572;
            FStar_Syntax_Syntax.residual_flags = uu____85581
          }  in
        let uu____85584 =
          let uu____85585 =
            let uu____85604 = elim_delayed_subst_binders bs  in
            let uu____85613 = elim_delayed_subst_term t2  in
            let uu____85616 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____85604, uu____85613, uu____85616)  in
          FStar_Syntax_Syntax.Tm_abs uu____85585  in
        mk1 uu____85584
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____85653 =
          let uu____85654 =
            let uu____85669 = elim_delayed_subst_binders bs  in
            let uu____85678 = elim_delayed_subst_comp c  in
            (uu____85669, uu____85678)  in
          FStar_Syntax_Syntax.Tm_arrow uu____85654  in
        mk1 uu____85653
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____85697 =
          let uu____85698 =
            let uu____85705 = elim_bv bv  in
            let uu____85706 = elim_delayed_subst_term phi  in
            (uu____85705, uu____85706)  in
          FStar_Syntax_Syntax.Tm_refine uu____85698  in
        mk1 uu____85697
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____85737 =
          let uu____85738 =
            let uu____85755 = elim_delayed_subst_term t2  in
            let uu____85758 = elim_delayed_subst_args args  in
            (uu____85755, uu____85758)  in
          FStar_Syntax_Syntax.Tm_app uu____85738  in
        mk1 uu____85737
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3899_85830 = p  in
              let uu____85831 =
                let uu____85832 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____85832  in
              {
                FStar_Syntax_Syntax.v = uu____85831;
                FStar_Syntax_Syntax.p =
                  (uu___3899_85830.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3903_85834 = p  in
              let uu____85835 =
                let uu____85836 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____85836  in
              {
                FStar_Syntax_Syntax.v = uu____85835;
                FStar_Syntax_Syntax.p =
                  (uu___3903_85834.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3909_85843 = p  in
              let uu____85844 =
                let uu____85845 =
                  let uu____85852 = elim_bv x  in
                  let uu____85853 = elim_delayed_subst_term t0  in
                  (uu____85852, uu____85853)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____85845  in
              {
                FStar_Syntax_Syntax.v = uu____85844;
                FStar_Syntax_Syntax.p =
                  (uu___3909_85843.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3915_85878 = p  in
              let uu____85879 =
                let uu____85880 =
                  let uu____85894 =
                    FStar_List.map
                      (fun uu____85920  ->
                         match uu____85920 with
                         | (x,b) ->
                             let uu____85937 = elim_pat x  in
                             (uu____85937, b)) pats
                     in
                  (fv, uu____85894)  in
                FStar_Syntax_Syntax.Pat_cons uu____85880  in
              {
                FStar_Syntax_Syntax.v = uu____85879;
                FStar_Syntax_Syntax.p =
                  (uu___3915_85878.FStar_Syntax_Syntax.p)
              }
          | uu____85952 -> p  in
        let elim_branch uu____85976 =
          match uu____85976 with
          | (pat,wopt,t3) ->
              let uu____86002 = elim_pat pat  in
              let uu____86005 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____86008 = elim_delayed_subst_term t3  in
              (uu____86002, uu____86005, uu____86008)
           in
        let uu____86013 =
          let uu____86014 =
            let uu____86037 = elim_delayed_subst_term t2  in
            let uu____86040 = FStar_List.map elim_branch branches  in
            (uu____86037, uu____86040)  in
          FStar_Syntax_Syntax.Tm_match uu____86014  in
        mk1 uu____86013
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____86171 =
          match uu____86171 with
          | (tc,topt) ->
              let uu____86206 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____86216 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____86216
                | FStar_Util.Inr c ->
                    let uu____86218 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____86218
                 in
              let uu____86219 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____86206, uu____86219)
           in
        let uu____86228 =
          let uu____86229 =
            let uu____86256 = elim_delayed_subst_term t2  in
            let uu____86259 = elim_ascription a  in
            (uu____86256, uu____86259, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____86229  in
        mk1 uu____86228
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3945_86322 = lb  in
          let uu____86323 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____86326 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3945_86322.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3945_86322.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____86323;
            FStar_Syntax_Syntax.lbeff =
              (uu___3945_86322.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____86326;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3945_86322.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3945_86322.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____86329 =
          let uu____86330 =
            let uu____86344 =
              let uu____86352 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____86352)  in
            let uu____86364 = elim_delayed_subst_term t2  in
            (uu____86344, uu____86364)  in
          FStar_Syntax_Syntax.Tm_let uu____86330  in
        mk1 uu____86329
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____86409 =
          let uu____86410 =
            let uu____86417 = elim_delayed_subst_term tm  in
            (uu____86417, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____86410  in
        mk1 uu____86409
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____86428 =
          let uu____86429 =
            let uu____86436 = elim_delayed_subst_term t2  in
            let uu____86439 = elim_delayed_subst_meta md  in
            (uu____86436, uu____86439)  in
          FStar_Syntax_Syntax.Tm_meta uu____86429  in
        mk1 uu____86428

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
      (fun uu___603_86448  ->
         match uu___603_86448 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____86452 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____86452
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
        let uu____86475 =
          let uu____86476 =
            let uu____86485 = elim_delayed_subst_term t  in
            (uu____86485, uopt)  in
          FStar_Syntax_Syntax.Total uu____86476  in
        mk1 uu____86475
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____86502 =
          let uu____86503 =
            let uu____86512 = elim_delayed_subst_term t  in
            (uu____86512, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____86503  in
        mk1 uu____86502
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3978_86521 = ct  in
          let uu____86522 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____86525 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____86536 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3978_86521.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3978_86521.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____86522;
            FStar_Syntax_Syntax.effect_args = uu____86525;
            FStar_Syntax_Syntax.flags = uu____86536
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___604_86539  ->
    match uu___604_86539 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____86553 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____86553
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____86592 =
          let uu____86599 = elim_delayed_subst_term t  in (m, uu____86599)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____86592
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____86611 =
          let uu____86620 = elim_delayed_subst_term t  in
          (m1, m2, uu____86620)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____86611
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
      (fun uu____86653  ->
         match uu____86653 with
         | (t,q) ->
             let uu____86672 = elim_delayed_subst_term t  in (uu____86672, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____86700  ->
         match uu____86700 with
         | (x,q) ->
             let uu____86719 =
               let uu___4002_86720 = x  in
               let uu____86721 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___4002_86720.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___4002_86720.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____86721
               }  in
             (uu____86719, q)) bs

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
            | (uu____86829,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____86861,FStar_Util.Inl t) ->
                let uu____86883 =
                  let uu____86890 =
                    let uu____86891 =
                      let uu____86906 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____86906)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____86891  in
                  FStar_Syntax_Syntax.mk uu____86890  in
                uu____86883 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____86919 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____86919 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____86951 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____87024 ->
                    let uu____87025 =
                      let uu____87034 =
                        let uu____87035 = FStar_Syntax_Subst.compress t4  in
                        uu____87035.FStar_Syntax_Syntax.n  in
                      (uu____87034, tc)  in
                    (match uu____87025 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____87064) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____87111) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____87156,FStar_Util.Inl uu____87157) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____87188 -> failwith "Impossible")
                 in
              (match uu____86951 with
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
          let uu____87327 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____87327 with
          | (univ_names1,binders1,tc) ->
              let uu____87401 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____87401)
  
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
          let uu____87455 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____87455 with
          | (univ_names1,binders1,tc) ->
              let uu____87529 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____87529)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____87571 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____87571 with
           | (univ_names1,binders1,typ1) ->
               let uu___4085_87611 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4085_87611.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4085_87611.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4085_87611.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4085_87611.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___4091_87626 = s  in
          let uu____87627 =
            let uu____87628 =
              let uu____87637 = FStar_List.map (elim_uvars env) sigs  in
              (uu____87637, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____87628  in
          {
            FStar_Syntax_Syntax.sigel = uu____87627;
            FStar_Syntax_Syntax.sigrng =
              (uu___4091_87626.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___4091_87626.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___4091_87626.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___4091_87626.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____87656 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____87656 with
           | (univ_names1,uu____87680,typ1) ->
               let uu___4105_87702 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4105_87702.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4105_87702.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4105_87702.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4105_87702.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____87709 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____87709 with
           | (univ_names1,uu____87733,typ1) ->
               let uu___4116_87755 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4116_87755.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4116_87755.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4116_87755.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4116_87755.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____87785 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____87785 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____87810 =
                            let uu____87811 =
                              let uu____87812 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____87812  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____87811
                             in
                          elim_delayed_subst_term uu____87810  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___4132_87815 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___4132_87815.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___4132_87815.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___4132_87815.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___4132_87815.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___4135_87816 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___4135_87816.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___4135_87816.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___4135_87816.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___4135_87816.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___4139_87823 = s  in
          let uu____87824 =
            let uu____87825 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____87825  in
          {
            FStar_Syntax_Syntax.sigel = uu____87824;
            FStar_Syntax_Syntax.sigrng =
              (uu___4139_87823.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___4139_87823.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___4139_87823.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___4139_87823.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____87829 = elim_uvars_aux_t env us [] t  in
          (match uu____87829 with
           | (us1,uu____87853,t1) ->
               let uu___4150_87875 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4150_87875.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4150_87875.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4150_87875.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4150_87875.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____87876 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____87879 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____87879 with
           | (univs1,binders,signature) ->
               let uu____87919 =
                 let uu____87924 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____87924 with
                 | (univs_opening,univs2) ->
                     let uu____87947 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____87947)
                  in
               (match uu____87919 with
                | (univs_opening,univs_closing) ->
                    let uu____87950 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____87956 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____87957 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____87956, uu____87957)  in
                    (match uu____87950 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____87983 =
                           match uu____87983 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____88001 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____88001 with
                                | (us1,t1) ->
                                    let uu____88012 =
                                      let uu____88021 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____88026 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____88021, uu____88026)  in
                                    (match uu____88012 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____88049 =
                                           let uu____88058 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____88063 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____88058, uu____88063)  in
                                         (match uu____88049 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____88087 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____88087
                                                 in
                                              let uu____88088 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____88088 with
                                               | (uu____88115,uu____88116,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____88139 =
                                                       let uu____88140 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____88140
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____88139
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____88149 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____88149 with
                           | (uu____88168,uu____88169,t1) -> t1  in
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
                             | uu____88245 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____88272 =
                               let uu____88273 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____88273.FStar_Syntax_Syntax.n  in
                             match uu____88272 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____88332 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____88366 =
                               let uu____88367 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____88367.FStar_Syntax_Syntax.n  in
                             match uu____88366 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____88390) ->
                                 let uu____88415 = destruct_action_body body
                                    in
                                 (match uu____88415 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____88464 ->
                                 let uu____88465 = destruct_action_body t  in
                                 (match uu____88465 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____88520 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____88520 with
                           | (action_univs,t) ->
                               let uu____88529 = destruct_action_typ_templ t
                                  in
                               (match uu____88529 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___4236_88576 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___4236_88576.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___4236_88576.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___4239_88578 = ed  in
                           let uu____88579 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____88580 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____88581 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____88582 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____88583 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____88584 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____88585 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____88586 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____88587 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____88588 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____88589 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____88590 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____88591 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____88592 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___4239_88578.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___4239_88578.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____88579;
                             FStar_Syntax_Syntax.bind_wp = uu____88580;
                             FStar_Syntax_Syntax.if_then_else = uu____88581;
                             FStar_Syntax_Syntax.ite_wp = uu____88582;
                             FStar_Syntax_Syntax.stronger = uu____88583;
                             FStar_Syntax_Syntax.close_wp = uu____88584;
                             FStar_Syntax_Syntax.assert_p = uu____88585;
                             FStar_Syntax_Syntax.assume_p = uu____88586;
                             FStar_Syntax_Syntax.null_wp = uu____88587;
                             FStar_Syntax_Syntax.trivial = uu____88588;
                             FStar_Syntax_Syntax.repr = uu____88589;
                             FStar_Syntax_Syntax.return_repr = uu____88590;
                             FStar_Syntax_Syntax.bind_repr = uu____88591;
                             FStar_Syntax_Syntax.actions = uu____88592;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___4239_88578.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___4242_88595 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___4242_88595.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___4242_88595.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___4242_88595.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___4242_88595.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___605_88616 =
            match uu___605_88616 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____88647 = elim_uvars_aux_t env us [] t  in
                (match uu____88647 with
                 | (us1,uu____88679,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___4257_88710 = sub_eff  in
            let uu____88711 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____88714 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___4257_88710.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___4257_88710.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____88711;
              FStar_Syntax_Syntax.lift = uu____88714
            }  in
          let uu___4260_88717 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___4260_88717.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___4260_88717.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___4260_88717.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___4260_88717.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____88727 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____88727 with
           | (univ_names1,binders1,comp1) ->
               let uu___4273_88767 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4273_88767.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4273_88767.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4273_88767.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4273_88767.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____88770 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____88771 -> s
  
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
        let uu____88820 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____88820 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____88842 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____88842 with
             | (uu____88849,head_def) ->
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
      let uu____88855 = FStar_Syntax_Util.head_and_args t  in
      match uu____88855 with
      | (head1,args) ->
          let uu____88900 =
            let uu____88901 = FStar_Syntax_Subst.compress head1  in
            uu____88901.FStar_Syntax_Syntax.n  in
          (match uu____88900 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____88908;
                  FStar_Syntax_Syntax.vars = uu____88909;_},us)
               -> aux fv us args
           | uu____88915 -> FStar_Pervasives_Native.None)
  