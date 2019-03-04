open Prims
let cases :
  'Auu____64041 'Auu____64042 .
    ('Auu____64041 -> 'Auu____64042) ->
      'Auu____64042 ->
        'Auu____64041 FStar_Pervasives_Native.option -> 'Auu____64042
  =
  fun f  ->
    fun d  ->
      fun uu___585_64062  ->
        match uu___585_64062 with
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
    match projectee with | Clos _0 -> true | uu____64160 -> false
  
let (__proj__Clos__item___0 :
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
      Prims.list * FStar_Syntax_Syntax.term * ((FStar_Syntax_Syntax.binder
      FStar_Pervasives_Native.option * closure) Prims.list *
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool))
  = fun projectee  -> match projectee with | Clos _0 -> _0 
let (uu___is_Univ : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____64273 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____64292 -> false
  
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
    match projectee with | Arg _0 -> true | uu____64472 -> false
  
let (__proj__Arg__item___0 :
  stack_elt -> (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)) =
  fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____64516 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range))
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____64560 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo) =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____64639 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env * branches * FStar_TypeChecker_Cfg.cfg * FStar_Range.range))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____64695 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * env *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
      FStar_Range.range))
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____64759 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Range.range))
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____64809 -> false
  
let (__proj__Meta__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.metadata * FStar_Range.range)) =
  fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____64855 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding *
      FStar_Range.range))
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____64899 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> FStar_TypeChecker_Cfg.cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____64923 -> false
  
let (__proj__Debug__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.term * FStar_Util.time)) =
  fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____64953 = FStar_Syntax_Util.head_and_args' t  in
    match uu____64953 with | (hd1,uu____64969) -> hd1
  
let mk :
  'Auu____64997 .
    'Auu____64997 ->
      FStar_Range.range -> 'Auu____64997 FStar_Syntax_Syntax.syntax
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
          let uu____65062 = FStar_ST.op_Bang r  in
          match uu____65062 with
          | FStar_Pervasives_Native.Some uu____65110 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____65187 =
      FStar_List.map
        (fun uu____65203  ->
           match uu____65203 with
           | (bopt,c) ->
               let uu____65217 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____65222 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____65217 uu____65222) env
       in
    FStar_All.pipe_right uu____65187 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___586_65230  ->
    match uu___586_65230 with
    | Clos (env,t,uu____65234,uu____65235) ->
        let uu____65282 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____65292 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____65282 uu____65292
    | Univ uu____65295 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___587_65304  ->
    match uu___587_65304 with
    | Arg (c,uu____65307,uu____65308) ->
        let uu____65309 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____65309
    | MemoLazy uu____65312 -> "MemoLazy"
    | Abs (uu____65320,bs,uu____65322,uu____65323,uu____65324) ->
        let uu____65329 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____65329
    | UnivArgs uu____65340 -> "UnivArgs"
    | Match uu____65348 -> "Match"
    | App (uu____65358,t,uu____65360,uu____65361) ->
        let uu____65362 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____65362
    | Meta (uu____65365,m,uu____65367) -> "Meta"
    | Let uu____65369 -> "Let"
    | Cfg uu____65379 -> "Cfg"
    | Debug (t,uu____65382) ->
        let uu____65383 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____65383
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____65397 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____65397 (FStar_String.concat "; ")
  
let is_empty : 'Auu____65412 . 'Auu____65412 Prims.list -> Prims.bool =
  fun uu___588_65420  ->
    match uu___588_65420 with | [] -> true | uu____65424 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        (fun uu___700_65457  ->
           match () with
           | () ->
               let uu____65458 =
                 FStar_List.nth env x.FStar_Syntax_Syntax.index  in
               FStar_Pervasives_Native.snd uu____65458) ()
      with
      | uu___699_65475 ->
          let uu____65476 =
            let uu____65478 = FStar_Syntax_Print.db_to_string x  in
            let uu____65480 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____65478
              uu____65480
             in
          failwith uu____65476
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____65491 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____65491
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____65498 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____65498
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____65505 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____65505
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
          let uu____65543 =
            FStar_List.fold_left
              (fun uu____65569  ->
                 fun u1  ->
                   match uu____65569 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____65594 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____65594 with
                        | (k_u,n1) ->
                            let uu____65612 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____65612
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____65543 with
          | (uu____65633,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 (fun uu___734_65659  ->
                    match () with
                    | () ->
                        let uu____65662 =
                          let uu____65663 = FStar_List.nth env x  in
                          FStar_Pervasives_Native.snd uu____65663  in
                        (match uu____65662 with
                         | Univ u3 ->
                             ((let uu____65682 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      cfg.FStar_TypeChecker_Cfg.tcenv)
                                   (FStar_Options.Other "univ_norm")
                                  in
                               if uu____65682
                               then
                                 let uu____65687 =
                                   FStar_Syntax_Print.univ_to_string u3  in
                                 FStar_Util.print1
                                   "Univ (in norm_universe): %s\n"
                                   uu____65687
                               else ());
                              aux u3)
                         | Dummy  -> [u2]
                         | uu____65692 ->
                             let uu____65693 =
                               let uu____65695 = FStar_Util.string_of_int x
                                  in
                               FStar_Util.format1
                                 "Impossible: universe variable u@%s bound to a term"
                                 uu____65695
                                in
                             failwith uu____65693)) ()
               with
               | uu____65705 ->
                   if
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else
                     (let uu____65711 =
                        let uu____65713 = FStar_Util.string_of_int x  in
                        FStar_String.op_Hat "Universe variable not found: u@"
                          uu____65713
                         in
                      failwith uu____65711))
          | FStar_Syntax_Syntax.U_unif uu____65718 when
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____65727 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____65736 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____65743 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____65743 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____65760 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____65760 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____65771 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____65781 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____65781 with
                                  | (uu____65788,m) -> n1 <= m))
                           in
                        if uu____65771 then rest1 else us1
                    | uu____65797 -> us1)
               | uu____65803 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____65807 = aux u3  in
              FStar_List.map
                (fun _65810  -> FStar_Syntax_Syntax.U_succ _65810)
                uu____65807
           in
        if
          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____65814 = aux u  in
           match uu____65814 with
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
            (fun uu____65983  ->
               let uu____65984 = FStar_Syntax_Print.tag_of_term t  in
               let uu____65986 = env_to_string env  in
               let uu____65988 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____65984 uu____65986 uu____65988);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____66001 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____66004 ->
                    let uu____66027 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____66027
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____66028 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____66029 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____66030 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____66031 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____66056 ->
                           let uu____66069 =
                             let uu____66071 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____66073 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____66071 uu____66073
                              in
                           failwith uu____66069
                       | uu____66078 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___589_66114  ->
                                         match uu___589_66114 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____66121 =
                                               let uu____66128 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____66128)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____66121
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___828_66140 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___828_66140.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___828_66140.FStar_Syntax_Syntax.sort)
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
                                              | uu____66146 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____66149 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___837_66154 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___837_66154.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___837_66154.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____66175 =
                        let uu____66176 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____66176  in
                      mk uu____66175 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____66184 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____66184  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____66186 = lookup_bvar env x  in
                    (match uu____66186 with
                     | Univ uu____66189 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___853_66194 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___853_66194.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___853_66194.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____66200,uu____66201) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____66292  ->
                              fun stack1  ->
                                match uu____66292 with
                                | (a,aq) ->
                                    let uu____66304 =
                                      let uu____66305 =
                                        let uu____66312 =
                                          let uu____66313 =
                                            let uu____66345 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____66345, false)  in
                                          Clos uu____66313  in
                                        (uu____66312, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____66305  in
                                    uu____66304 :: stack1) args)
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
                    let uu____66535 = close_binders cfg env bs  in
                    (match uu____66535 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,uu____66585) when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    ->
                    inline_closure_env cfg env stack
                      x.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____66596 =
                      let uu____66609 =
                        let uu____66618 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____66618]  in
                      close_binders cfg env uu____66609  in
                    (match uu____66596 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____66663 =
                             let uu____66664 =
                               let uu____66671 =
                                 let uu____66672 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____66672
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____66671, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____66664  in
                           mk uu____66663 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____66771 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____66771
                      | FStar_Util.Inr c ->
                          let uu____66785 = close_comp cfg env c  in
                          FStar_Util.Inr uu____66785
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____66804 =
                        let uu____66805 =
                          let uu____66832 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____66832, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____66805  in
                      mk uu____66804 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____66878 =
                            let uu____66879 =
                              let uu____66886 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____66886, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____66879  in
                          mk uu____66878 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____66941  -> dummy :: env1) env
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
                    let uu____66962 =
                      let uu____66973 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____66973
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____66995 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___945_67011 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___945_67011.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___945_67011.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____66995))
                       in
                    (match uu____66962 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___950_67029 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___950_67029.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___950_67029.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___950_67029.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___950_67029.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____67046,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____67112  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____67129 =
                          FStar_Syntax_Syntax.is_top_level lbs  in
                        if uu____67129
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____67144  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____67168 =
                          FStar_Syntax_Syntax.is_top_level lbs  in
                        if uu____67168
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___973_67179 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___973_67179.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___973_67179.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___976_67180 = lb  in
                      let uu____67181 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___976_67180.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___976_67180.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____67181;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___976_67180.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___976_67180.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____67213  -> fun env1  -> dummy :: env1)
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
            (fun uu____67305  ->
               let uu____67306 = FStar_Syntax_Print.tag_of_term t  in
               let uu____67308 = env_to_string env  in
               let uu____67310 = stack_to_string stack  in
               let uu____67312 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____67306 uu____67308 uu____67310 uu____67312);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____67319,uu____67320),aq,r))::stack1
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
               let uu____67401 = close_binders cfg env' bs  in
               (match uu____67401 with
                | (bs1,uu____67417) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____67437 =
                      let uu___1034_67440 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___1034_67440.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___1034_67440.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____67437)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____67496 =
                 match uu____67496 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____67611 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____67642 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____67731  ->
                                     fun uu____67732  ->
                                       match (uu____67731, uu____67732) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____67882 = norm_pat env4 p1
                                              in
                                           (match uu____67882 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____67642 with
                            | (pats1,env4) ->
                                ((let uu___1071_68052 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___1071_68052.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___1075_68073 = x  in
                             let uu____68074 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1075_68073.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1075_68073.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____68074
                             }  in
                           ((let uu___1078_68088 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___1078_68088.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___1082_68099 = x  in
                             let uu____68100 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1082_68099.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1082_68099.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____68100
                             }  in
                           ((let uu___1085_68114 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___1085_68114.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___1091_68130 = x  in
                             let uu____68131 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1091_68130.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1091_68130.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____68131
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___1095_68148 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___1095_68148.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____68153 = norm_pat env2 pat  in
                     (match uu____68153 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____68222 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____68222
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____68241 =
                   let uu____68242 =
                     let uu____68265 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____68265)  in
                   FStar_Syntax_Syntax.Tm_match uu____68242  in
                 mk uu____68241 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____68380 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____68489  ->
                                       match uu____68489 with
                                       | (a,q) ->
                                           let uu____68516 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____68516, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____68380
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____68529 =
                       let uu____68536 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____68536)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____68529
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____68548 =
                       let uu____68557 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____68557)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____68548
                 | uu____68562 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____68568 -> failwith "Impossible: unexpected stack element")

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
            let uu____68584 =
              let uu____68585 = inline_closure_env cfg env [] t  in
              FStar_Syntax_Syntax.Meta uu____68585  in
            FStar_Pervasives_Native.Some uu____68584
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
        let uu____68602 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____68686  ->
                  fun uu____68687  ->
                    match (uu____68686, uu____68687) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___1148_68827 = b  in
                          let uu____68828 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1148_68827.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1148_68827.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____68828
                          }  in
                        let imp1 = close_imp cfg env1 imp  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp1) :: out))) (env, []))
           in
        match uu____68602 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____68970 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____68983 = inline_closure_env cfg env [] t  in
                 let uu____68984 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____68983 uu____68984
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____68997 = inline_closure_env cfg env [] t  in
                 let uu____68998 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____68997 uu____68998
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____69052  ->
                           match uu____69052 with
                           | (a,q) ->
                               let uu____69073 =
                                 inline_closure_env cfg env [] a  in
                               (uu____69073, q)))
                    in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___590_69090  ->
                           match uu___590_69090 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____69094 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____69094
                           | f -> f))
                    in
                 let uu____69098 =
                   let uu___1181_69099 = c1  in
                   let uu____69100 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____69100;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___1181_69099.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____69098)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___591_69110  ->
            match uu___591_69110 with
            | FStar_Syntax_Syntax.DECREASES uu____69112 -> false
            | uu____69116 -> true))

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
                   (fun uu___592_69135  ->
                      match uu___592_69135 with
                      | FStar_Syntax_Syntax.DECREASES uu____69137 -> false
                      | uu____69141 -> true))
               in
            let rc1 =
              let uu___1198_69144 = rc  in
              let uu____69145 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___1198_69144.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____69145;
                FStar_Syntax_Syntax.residual_flags = flags
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____69154 -> lopt

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
    let uu____69224 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____69224 with
    | FStar_Pervasives_Native.Some e ->
        let uu____69263 = FStar_Syntax_Embeddings.unembed e t  in
        uu____69263 true FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____69287 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv * 'Auu____69287)
        FStar_Pervasives_Native.option * closure) Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____69349  ->
           fun subst1  ->
             match uu____69349 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____69390,uu____69391)) ->
                      let uu____69452 = b  in
                      (match uu____69452 with
                       | (bv,uu____69460) ->
                           let uu____69461 =
                             let uu____69463 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____69463  in
                           if uu____69461
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____69471 = unembed_binder term1  in
                              match uu____69471 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____69478 =
                                      let uu___1233_69479 = bv  in
                                      let uu____69480 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___1233_69479.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___1233_69479.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____69480
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____69478
                                     in
                                  let b_for_x =
                                    let uu____69486 =
                                      let uu____69493 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____69493)
                                       in
                                    FStar_Syntax_Syntax.NT uu____69486  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___593_69509  ->
                                         match uu___593_69509 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____69511,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____69513;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____69514;_})
                                             ->
                                             let uu____69519 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____69519
                                         | uu____69521 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____69523 -> subst1)) env []
  
let reduce_primops :
  'Auu____69546 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'Auu____69546)
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
            (let uu____69600 = FStar_Syntax_Util.head_and_args tm  in
             match uu____69600 with
             | (head1,args) ->
                 let uu____69645 =
                   let uu____69646 = FStar_Syntax_Util.un_uinst head1  in
                   uu____69646.FStar_Syntax_Syntax.n  in
                 (match uu____69645 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____69652 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                      (match uu____69652 with
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
                                (fun uu____69681  ->
                                   let uu____69682 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name
                                      in
                                   let uu____69684 =
                                     FStar_Util.string_of_int l  in
                                   let uu____69692 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____69682 uu____69684 uu____69692);
                              tm)
                           else
                             (let uu____69697 =
                                if l = prim_step.FStar_TypeChecker_Cfg.arity
                                then (args, [])
                                else
                                  FStar_List.splitAt
                                    prim_step.FStar_TypeChecker_Cfg.arity
                                    args
                                 in
                              match uu____69697 with
                              | (args_1,args_2) ->
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____69787  ->
                                        let uu____69788 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____69788);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____69793  ->
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
                                           (fun uu____69809  ->
                                              let uu____69810 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____69810);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____69818  ->
                                              let uu____69819 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____69821 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____69819 uu____69821);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____69824 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____69828  ->
                                 let uu____69829 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____69829);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____69835  ->
                            let uu____69836 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____69836);
                       (match args with
                        | (a1,uu____69842)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____69867 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____69881  ->
                            let uu____69882 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____69882);
                       (match args with
                        | (t,uu____69888)::(r,uu____69890)::[] ->
                            let uu____69931 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____69931 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____69937 -> tm))
                  | uu____69948 -> tm))
  
let reduce_equality :
  'Auu____69960 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'Auu____69960)
          FStar_Pervasives_Native.option * closure) Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun tm  ->
        reduce_primops norm_cb
          (let uu___1321_70013 = cfg  in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___1323_70016 = FStar_TypeChecker_Cfg.default_steps  in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.nbe_step);
                  FStar_TypeChecker_Cfg.for_extraction =
                    (uu___1323_70016.FStar_TypeChecker_Cfg.for_extraction)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___1321_70013.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___1321_70013.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___1321_70013.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___1321_70013.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___1321_70013.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___1321_70013.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___1321_70013.FStar_TypeChecker_Cfg.reifying)
           }) tm
  
type norm_request_t =
  | Norm_request_none 
  | Norm_request_ready 
  | Norm_request_requires_rejig 
let (uu___is_Norm_request_none : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_none  -> true | uu____70027 -> false
  
let (uu___is_Norm_request_ready : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_ready  -> true | uu____70038 -> false
  
let (uu___is_Norm_request_requires_rejig : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Norm_request_requires_rejig  -> true
    | uu____70049 -> false
  
let (is_norm_request :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.args -> norm_request_t) =
  fun hd1  ->
    fun args  ->
      let aux min_args =
        let uu____70070 = FStar_All.pipe_right args FStar_List.length  in
        FStar_All.pipe_right uu____70070
          (fun n1  ->
             if n1 < min_args
             then Norm_request_none
             else
               if n1 = min_args
               then Norm_request_ready
               else Norm_request_requires_rejig)
         in
      let uu____70102 =
        let uu____70103 = FStar_Syntax_Util.un_uinst hd1  in
        uu____70103.FStar_Syntax_Syntax.n  in
      match uu____70102 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          -> aux (Prims.parse_int "2")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          aux (Prims.parse_int "1")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          aux (Prims.parse_int "3")
      | uu____70112 -> Norm_request_none
  
let (should_consider_norm_requests : FStar_TypeChecker_Cfg.cfg -> Prims.bool)
  =
  fun cfg  ->
    (Prims.op_Negation
       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
      &&
      (let uu____70121 =
         FStar_Ident.lid_equals
           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
           FStar_Parser_Const.prims_lid
          in
       Prims.op_Negation uu____70121)
  
let (rejig_norm_request :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term)
  =
  fun hd1  ->
    fun args  ->
      let uu____70134 =
        let uu____70135 = FStar_Syntax_Util.un_uinst hd1  in
        uu____70135.FStar_Syntax_Syntax.n  in
      match uu____70134 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          ->
          (match args with
           | t1::t2::rest when
               (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____70193 = FStar_Syntax_Util.mk_app hd1 [t1; t2]  in
               FStar_Syntax_Util.mk_app uu____70193 rest
           | uu____70220 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize_term")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          (match args with
           | t::rest when (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____70260 = FStar_Syntax_Util.mk_app hd1 [t]  in
               FStar_Syntax_Util.mk_app uu____70260 rest
           | uu____70279 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          (match args with
           | t1::t2::t3::rest when
               (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____70353 = FStar_Syntax_Util.mk_app hd1 [t1; t2; t3]
                  in
               FStar_Syntax_Util.mk_app uu____70353 rest
           | uu____70388 ->
               failwith "Impossible! invalid rejig_norm_request for norm")
      | uu____70390 ->
          let uu____70391 =
            let uu____70393 = FStar_Syntax_Print.term_to_string hd1  in
            FStar_String.op_Hat
              "Impossible! invalid rejig_norm_request for: %s" uu____70393
             in
          failwith uu____70391
  
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s  ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
  
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___594_70414  ->
    match uu___594_70414 with
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
        let uu____70421 =
          let uu____70424 =
            let uu____70425 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            FStar_TypeChecker_Env.UnfoldOnly uu____70425  in
          [uu____70424]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____70421
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____70433 =
          let uu____70436 =
            let uu____70437 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            FStar_TypeChecker_Env.UnfoldFully uu____70437  in
          [uu____70436]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____70433
    | FStar_Syntax_Embeddings.UnfoldAttr names1 ->
        let uu____70445 =
          let uu____70448 =
            let uu____70449 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            FStar_TypeChecker_Env.UnfoldAttr uu____70449  in
          [uu____70448]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____70445
    | FStar_Syntax_Embeddings.NBE  -> [FStar_TypeChecker_Env.NBE]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  = fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____70474 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term * 'Auu____70474) Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list * FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____70525 =
            let uu____70530 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____70530 s  in
          match uu____70525 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____70546 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____70546
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
        | uu____70581::(tm,uu____70583)::[] ->
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
        | (tm,uu____70612)::[] ->
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
        | (steps,uu____70633)::uu____70634::(tm,uu____70636)::[] ->
            let add_exclude s z =
              let uu____70674 =
                FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s  in
              if uu____70674
              then s
              else (FStar_TypeChecker_Env.Exclude z) :: s  in
            let uu____70681 =
              let uu____70686 = full_norm steps  in parse_steps uu____70686
               in
            (match uu____70681 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = FStar_TypeChecker_Env.Beta :: s  in
                 let s2 = add_exclude s1 FStar_TypeChecker_Env.Zeta  in
                 let s3 = add_exclude s2 FStar_TypeChecker_Env.Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____70725 -> FStar_Pervasives_Native.None
  
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun s  ->
      fun tm  ->
        let delta_level =
          let uu____70757 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___595_70764  ->
                    match uu___595_70764 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____70766 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____70768 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____70772 -> true
                    | uu____70776 -> false))
             in
          if uu____70757
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta]  in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____70786  ->
             let uu____70787 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____70787);
        (let tm_norm =
           let uu____70791 =
             let uu____70806 = FStar_TypeChecker_Cfg.cfg_env cfg  in
             uu____70806.FStar_TypeChecker_Env.nbe  in
           uu____70791 s cfg.FStar_TypeChecker_Cfg.tcenv tm  in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____70810  ->
              let uu____70811 = FStar_Syntax_Print.term_to_string tm_norm  in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____70811);
         tm_norm)
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___596_70822  ->
    match uu___596_70822 with
    | (App
        (uu____70826,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____70827;
                       FStar_Syntax_Syntax.vars = uu____70828;_},uu____70829,uu____70830))::uu____70831
        -> true
    | uu____70837 -> false
  
let firstn :
  'Auu____70848 .
    Prims.int ->
      'Auu____70848 Prims.list ->
        ('Auu____70848 Prims.list * 'Auu____70848 Prims.list)
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack  ->
      let rec drop_irrel uu___597_70905 =
        match uu___597_70905 with
        | (MemoLazy uu____70910)::s -> drop_irrel s
        | (UnivArgs uu____70920)::s -> drop_irrel s
        | s -> s  in
      let uu____70933 = drop_irrel stack  in
      match uu____70933 with
      | (App
          (uu____70937,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____70938;
                         FStar_Syntax_Syntax.vars = uu____70939;_},uu____70940,uu____70941))::uu____70942
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____70947 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____70976) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____70986) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____71007  ->
                  match uu____71007 with
                  | (a,uu____71018) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____71029 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____71054 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____71056 -> false
    | FStar_Syntax_Syntax.Tm_type uu____71070 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____71072 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____71074 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____71076 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____71078 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____71081 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____71089 -> false
    | FStar_Syntax_Syntax.Tm_let uu____71097 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____71112 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____71132 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____71148 -> true
    | FStar_Syntax_Syntax.Tm_match uu____71156 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____71228  ->
                   match uu____71228 with
                   | (a,uu____71239) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____71250) ->
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
                     (fun uu____71382  ->
                        match uu____71382 with
                        | (a,uu____71393) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____71402,uu____71403,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____71409,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____71415 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____71425 -> false
            | FStar_Syntax_Syntax.Meta_named uu____71427 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____71438 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____71449 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Should_unfold_fully  -> true
    | uu____71460 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Should_unfold_reify  -> true
    | uu____71471 -> false
  
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
            let uu____71504 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo
               in
            match uu____71504 with
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
              (fun uu____71703  ->
                 fun uu____71704  ->
                   match (uu____71703, uu____71704) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____71810 =
            match uu____71810 with
            | (x,y,z) ->
                let uu____71830 = FStar_Util.string_of_bool x  in
                let uu____71832 = FStar_Util.string_of_bool y  in
                let uu____71834 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____71830 uu____71832
                  uu____71834
             in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg  in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____71862  ->
                    let uu____71863 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____71865 = FStar_Util.string_of_bool b  in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____71863 uu____71865);
               if b then reif else no)
            else
              if
                (let uu____71880 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                 FStar_Option.isSome uu____71880)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____71885  ->
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
                          ((is_rec,uu____71920),uu____71921);
                        FStar_Syntax_Syntax.sigrng = uu____71922;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____71924;
                        FStar_Syntax_Syntax.sigattrs = uu____71925;_},uu____71926),uu____71927),uu____71928,uu____71929,uu____71930)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____72037  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____72039,uu____72040,uu____72041,uu____72042) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____72109  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____72112),uu____72113);
                        FStar_Syntax_Syntax.sigrng = uu____72114;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____72116;
                        FStar_Syntax_Syntax.sigattrs = uu____72117;_},uu____72118),uu____72119),uu____72120,uu____72121,uu____72122)
                     when
                     is_rec &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____72229  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____72231,FStar_Pervasives_Native.Some
                    uu____72232,uu____72233,uu____72234) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____72302  ->
                           let uu____72303 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____72303);
                      (let uu____72306 =
                         let uu____72318 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____72344 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____72344
                            in
                         let uu____72356 =
                           let uu____72368 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____72394 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____72394
                              in
                           let uu____72410 =
                             let uu____72422 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____72448 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____72448
                                in
                             [uu____72422]  in
                           uu____72368 :: uu____72410  in
                         uu____72318 :: uu____72356  in
                       comb_or uu____72306))
                 | (uu____72496,uu____72497,FStar_Pervasives_Native.Some
                    uu____72498,uu____72499) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____72567  ->
                           let uu____72568 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____72568);
                      (let uu____72571 =
                         let uu____72583 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____72609 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____72609
                            in
                         let uu____72621 =
                           let uu____72633 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____72659 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____72659
                              in
                           let uu____72675 =
                             let uu____72687 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____72713 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____72713
                                in
                             [uu____72687]  in
                           uu____72633 :: uu____72675  in
                         uu____72583 :: uu____72621  in
                       comb_or uu____72571))
                 | (uu____72761,uu____72762,uu____72763,FStar_Pervasives_Native.Some
                    uu____72764) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____72832  ->
                           let uu____72833 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____72833);
                      (let uu____72836 =
                         let uu____72848 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____72874 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____72874
                            in
                         let uu____72886 =
                           let uu____72898 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____72924 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____72924
                              in
                           let uu____72940 =
                             let uu____72952 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____72978 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____72978
                                in
                             [uu____72952]  in
                           uu____72898 :: uu____72940  in
                         uu____72848 :: uu____72886  in
                       comb_or uu____72836))
                 | uu____73026 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____73072  ->
                           let uu____73073 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____73075 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____73077 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level
                              in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____73073 uu____73075 uu____73077);
                      (let uu____73080 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___598_73086  ->
                                 match uu___598_73086 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.InliningDelta  ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____73092 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv
                                        in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____73092 l))
                          in
                       FStar_All.pipe_left yesno uu____73080)))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____73108  ->
               let uu____73109 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____73111 =
                 let uu____73113 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____73113  in
               let uu____73114 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____73109 uu____73111 uu____73114);
          (match res with
           | (false ,uu____73117,uu____73118) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____73143 ->
               let uu____73153 =
                 let uu____73155 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____73155
                  in
               FStar_All.pipe_left failwith uu____73153)
  
let decide_unfolding :
  'Auu____73174 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'Auu____73174 ->
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
                    let uu___1740_73243 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___1742_73246 =
                           cfg.FStar_TypeChecker_Cfg.steps  in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1742_73246.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1742_73246.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1742_73246.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1742_73246.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1742_73246.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1742_73246.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1742_73246.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___1742_73246.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1742_73246.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1742_73246.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1742_73246.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1742_73246.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1742_73246.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1742_73246.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1742_73246.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1742_73246.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1742_73246.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1742_73246.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___1742_73246.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1742_73246.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1742_73246.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1742_73246.FStar_TypeChecker_Cfg.for_extraction)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1740_73243.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1740_73243.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___1740_73243.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1740_73243.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1740_73243.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1740_73243.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1740_73243.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1740_73243.FStar_TypeChecker_Cfg.reifying)
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
                        let uu____73308 = push1 e t  in (UnivArgs (us, r)) ::
                          uu____73308
                    | h::t -> e :: h :: t  in
                  let ref =
                    let uu____73320 =
                      let uu____73327 =
                        let uu____73328 =
                          let uu____73329 = FStar_Syntax_Syntax.lid_of_fv fv
                             in
                          FStar_Const.Const_reflect uu____73329  in
                        FStar_Syntax_Syntax.Tm_constant uu____73328  in
                      FStar_Syntax_Syntax.mk uu____73327  in
                    uu____73320 FStar_Pervasives_Native.None
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
    let uu____73398 =
      let uu____73399 = FStar_Syntax_Subst.compress t  in
      uu____73399.FStar_Syntax_Syntax.n  in
    match uu____73398 with
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____73430 =
          let uu____73431 = FStar_Syntax_Util.un_uinst hd1  in
          uu____73431.FStar_Syntax_Syntax.n  in
        (match uu____73430 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStar_List.length args) = (Prims.parse_int "3"))
             ->
             let f =
               let uu____73448 =
                 let uu____73455 =
                   let uu____73466 = FStar_All.pipe_right args FStar_List.tl
                      in
                   FStar_All.pipe_right uu____73466 FStar_List.tl  in
                 FStar_All.pipe_right uu____73455 FStar_List.hd  in
               FStar_All.pipe_right uu____73448 FStar_Pervasives_Native.fst
                in
             FStar_Pervasives_Native.Some f
         | uu____73565 -> FStar_Pervasives_Native.None)
    | uu____73566 -> FStar_Pervasives_Native.None
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____73845 ->
                   let uu____73868 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____73868
               | uu____73871 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____73881  ->
               let uu____73882 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____73884 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____73886 = FStar_Syntax_Print.term_to_string t1  in
               let uu____73888 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____73896 =
                 let uu____73898 =
                   let uu____73901 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____73901
                    in
                 stack_to_string uu____73898  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____73882 uu____73884 uu____73886 uu____73888 uu____73896);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____73929  ->
               let uu____73930 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____73930);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____73936  ->
                     let uu____73937 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____73937);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____73940 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____73944  ->
                     let uu____73945 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____73945);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____73948 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____73952  ->
                     let uu____73953 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____73953);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____73956 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____73960  ->
                     let uu____73961 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____73961);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____73964;
                 FStar_Syntax_Syntax.fv_delta = uu____73965;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____73969  ->
                     let uu____73970 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____73970);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____73973;
                 FStar_Syntax_Syntax.fv_delta = uu____73974;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____73975);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____73985  ->
                     let uu____73986 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____73986);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid
                  in
               let uu____73992 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
               (match uu____73992 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level _73995) when
                    _73995 = (Prims.parse_int "0") ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____73999  ->
                          let uu____74000 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____74000);
                     rebuild cfg env stack t1)
                | uu____74003 ->
                    let uu____74006 =
                      decide_unfolding cfg env stack
                        t1.FStar_Syntax_Syntax.pos fv qninfo
                       in
                    (match uu____74006 with
                     | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                         do_unfold_fv cfg1 env stack1 t1 qninfo fv
                     | FStar_Pervasives_Native.None  ->
                         rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_quoted uu____74033 ->
               let uu____74040 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____74040
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____74068 = is_norm_request hd1 args  in
                  uu____74068 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu____74074 = rejig_norm_request hd1 args  in
                 norm cfg env stack uu____74074))
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____74102 = is_norm_request hd1 args  in
                  uu____74102 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___1850_74109 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1852_74112 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1852_74112.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1852_74112.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1852_74112.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___1852_74112.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1852_74112.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1852_74112.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1852_74112.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1852_74112.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1852_74112.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1852_74112.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1852_74112.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1852_74112.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1852_74112.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1852_74112.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1852_74112.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1852_74112.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1852_74112.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1852_74112.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1852_74112.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1852_74112.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1852_74112.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1852_74112.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1852_74112.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1850_74109.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1850_74109.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1850_74109.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1850_74109.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1850_74109.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1850_74109.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____74119 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____74119 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____74155  ->
                                 fun stack1  ->
                                   match uu____74155 with
                                   | (a,aq) ->
                                       let uu____74167 =
                                         let uu____74168 =
                                           let uu____74175 =
                                             let uu____74176 =
                                               let uu____74208 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____74208, false)
                                                in
                                             Clos uu____74176  in
                                           (uu____74175, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____74168  in
                                       uu____74167 :: stack1) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____74298  ->
                            let uu____74299 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____74299);
                       norm cfg env stack1 hd1))
                 | FStar_Pervasives_Native.Some (s,tm) when is_nbe_request s
                     ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____74326 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting NBE request on %s ... \n" uu____74326)
                      else ();
                      (let tm' = closure_as_term cfg env tm  in
                       let start = FStar_Util.now ()  in
                       let tm_norm = nbe_eval cfg s tm'  in
                       let fin = FStar_Util.now ()  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         (let uu____74337 =
                            let uu____74339 =
                              let uu____74341 =
                                FStar_Util.time_diff start fin  in
                              FStar_Pervasives_Native.snd uu____74341  in
                            FStar_Util.string_of_int uu____74339  in
                          let uu____74348 =
                            FStar_Syntax_Print.term_to_string tm'  in
                          let uu____74350 =
                            FStar_Syntax_Print.term_to_string tm_norm  in
                          FStar_Util.print3 "NBE'd (%s ms) %s\n\tto %s\n"
                            uu____74337 uu____74348 uu____74350)
                       else ();
                       norm cfg env stack tm_norm))
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____74369 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting norm request on %s ... \n" uu____74369)
                      else ();
                      (let delta_level =
                         let uu____74377 =
                           FStar_All.pipe_right s
                             (FStar_Util.for_some
                                (fun uu___599_74384  ->
                                   match uu___599_74384 with
                                   | FStar_TypeChecker_Env.UnfoldUntil
                                       uu____74386 -> true
                                   | FStar_TypeChecker_Env.UnfoldOnly
                                       uu____74388 -> true
                                   | FStar_TypeChecker_Env.UnfoldFully
                                       uu____74392 -> true
                                   | uu____74396 -> false))
                            in
                         if uu____74377
                         then
                           [FStar_TypeChecker_Env.Unfold
                              FStar_Syntax_Syntax.delta_constant]
                         else [FStar_TypeChecker_Env.NoDelta]  in
                       let cfg'1 =
                         let uu___1893_74404 = cfg  in
                         let uu____74405 =
                           let uu___1895_74406 =
                             FStar_TypeChecker_Cfg.to_fsteps s  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.unfold_only);
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               true;
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___1895_74406.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         {
                           FStar_TypeChecker_Cfg.steps = uu____74405;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___1893_74404.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___1893_74404.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = delta_level;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___1893_74404.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong =
                             (uu___1893_74404.FStar_TypeChecker_Cfg.strong);
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___1893_74404.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___1893_74404.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let stack' =
                         let tail1 = (Cfg cfg) :: stack  in
                         if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           let uu____74414 =
                             let uu____74415 =
                               let uu____74420 = FStar_Util.now ()  in
                               (t1, uu____74420)  in
                             Debug uu____74415  in
                           uu____74414 :: tail1
                         else tail1  in
                       norm cfg'1 env stack' tm))))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____74425 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____74425
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____74436 =
                      let uu____74443 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____74443, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____74436  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____74452 = lookup_bvar env x  in
               (match uu____74452 with
                | Univ uu____74453 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                    then
                      let uu____74507 = FStar_ST.op_Bang r  in
                      (match uu____74507 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____74625  ->
                                 let uu____74626 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____74628 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____74626
                                   uu____74628);
                            (let uu____74631 = maybe_weakly_reduced t'  in
                             if uu____74631
                             then
                               match stack with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____74634 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____74711)::uu____74712 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____74723,uu____74724))::stack_rest ->
                    (match c with
                     | Univ uu____74728 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____74737 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____74767  ->
                                    let uu____74768 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____74768);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____74804  ->
                                    let uu____74805 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____74805);
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
                       (fun uu____74875  ->
                          let uu____74876 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____74876);
                     norm cfg env stack1 t1)
                | (Match uu____74879)::uu____74880 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____74895 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____74895 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____74931  -> dummy :: env1) env)
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
                                          let uu____74975 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____74975)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_74983 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_74983.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_74983.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____74984 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____74990  ->
                                 let uu____74991 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____74991);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_75006 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_75006.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_75006.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_75006.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_75006.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_75006.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_75006.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_75006.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_75006.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____75010)::uu____75011 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____75022 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____75022 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____75058  -> dummy :: env1) env)
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
                                          let uu____75102 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____75102)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_75110 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_75110.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_75110.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____75111 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____75117  ->
                                 let uu____75118 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____75118);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_75133 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_75133.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_75133.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_75133.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_75133.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_75133.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_75133.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_75133.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_75133.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____75137)::uu____75138 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____75151 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____75151 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____75187  -> dummy :: env1) env)
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
                                          let uu____75231 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____75231)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_75239 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_75239.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_75239.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____75240 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____75246  ->
                                 let uu____75247 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____75247);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_75262 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_75262.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_75262.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_75262.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_75262.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_75262.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_75262.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_75262.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_75262.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____75266)::uu____75267 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____75282 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____75282 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____75318  -> dummy :: env1) env)
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
                                          let uu____75362 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____75362)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_75370 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_75370.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_75370.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____75371 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____75377  ->
                                 let uu____75378 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____75378);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_75393 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_75393.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_75393.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_75393.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_75393.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_75393.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_75393.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_75393.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_75393.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____75397)::uu____75398 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____75413 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____75413 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____75449  -> dummy :: env1) env)
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
                                          let uu____75493 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____75493)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_75501 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_75501.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_75501.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____75502 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____75508  ->
                                 let uu____75509 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____75509);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_75524 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_75524.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_75524.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_75524.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_75524.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_75524.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_75524.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_75524.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_75524.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____75528)::uu____75529 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____75548 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____75548 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____75584  -> dummy :: env1) env)
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
                                          let uu____75628 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____75628)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_75636 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_75636.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_75636.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____75637 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____75643  ->
                                 let uu____75644 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____75644);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_75659 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_75659.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_75659.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_75659.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_75659.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_75659.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_75659.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_75659.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_75659.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____75667 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____75667 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____75703  -> dummy :: env1) env)
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
                                          let uu____75747 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____75747)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_75755 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_75755.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_75755.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____75756 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____75762  ->
                                 let uu____75763 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____75763);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_75778 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_75778.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_75778.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_75778.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_75778.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_75778.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_75778.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_75778.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_75778.FStar_TypeChecker_Cfg.reifying)
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
                      (fun uu____75822  ->
                         fun stack1  ->
                           match uu____75822 with
                           | (a,aq) ->
                               let uu____75834 =
                                 let uu____75835 =
                                   let uu____75842 =
                                     let uu____75843 =
                                       let uu____75875 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____75875, false)  in
                                     Clos uu____75843  in
                                   (uu____75842, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____75835  in
                               uu____75834 :: stack1) args)
                  in
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____75965  ->
                     let uu____75966 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____75966);
                norm cfg env stack1 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,uu____75980) when
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
                             ((let uu___2047_76025 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2047_76025.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2047_76025.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____76026 ->
                      let uu____76041 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____76041)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____76045 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____76045 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____76076 =
                          let uu____76077 =
                            let uu____76084 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___2056_76090 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2056_76090.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___2056_76090.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____76084)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____76077  in
                        mk uu____76076 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____76114 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____76114
               else
                 (let uu____76117 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____76117 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____76125 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____76151  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____76125 c1  in
                      let t2 =
                        let uu____76175 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____76175 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____76288)::uu____76289 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____76302  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____76304)::uu____76305 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____76316  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____76318,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____76319;
                                   FStar_Syntax_Syntax.vars = uu____76320;_},uu____76321,uu____76322))::uu____76323
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____76330  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____76332)::uu____76333 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____76344  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____76346 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____76349  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____76354  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____76380 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____76380
                         | FStar_Util.Inr c ->
                             let uu____76394 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____76394
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____76417 =
                               let uu____76418 =
                                 let uu____76445 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____76445, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____76418
                                in
                             mk uu____76417 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____76480 ->
                           let uu____76481 =
                             let uu____76482 =
                               let uu____76483 =
                                 let uu____76510 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____76510, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____76483
                                in
                             mk uu____76482 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____76481))))
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
                   let uu___2135_76588 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___2137_76591 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___2137_76591.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___2135_76588.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___2135_76588.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___2135_76588.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___2135_76588.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___2135_76588.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___2135_76588.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___2135_76588.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___2135_76588.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____76632 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____76632 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___2150_76652 = cfg  in
                               let uu____76653 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2150_76652.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____76653;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2150_76652.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2150_76652.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2150_76652.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___2150_76652.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2150_76652.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2150_76652.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2150_76652.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____76660 =
                                 let uu____76661 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____76661  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____76660
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___2157_76664 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___2157_76664.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2157_76664.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2157_76664.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2157_76664.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____76665 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____76665
           | FStar_Syntax_Syntax.Tm_let
               ((uu____76678,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____76679;
                               FStar_Syntax_Syntax.lbunivs = uu____76680;
                               FStar_Syntax_Syntax.lbtyp = uu____76681;
                               FStar_Syntax_Syntax.lbeff = uu____76682;
                               FStar_Syntax_Syntax.lbdef = uu____76683;
                               FStar_Syntax_Syntax.lbattrs = uu____76684;
                               FStar_Syntax_Syntax.lbpos = uu____76685;_}::uu____76686),uu____76687)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name
                   cfg.FStar_TypeChecker_Cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____76733 =
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
               if uu____76733
               then
                 let binder =
                   let uu____76737 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____76737  in
                 let env1 =
                   let uu____76747 =
                     let uu____76754 =
                       let uu____76755 =
                         let uu____76787 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____76787,
                           false)
                          in
                       Clos uu____76755  in
                     ((FStar_Pervasives_Native.Some binder), uu____76754)  in
                   uu____76747 :: env  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____76884  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                 then
                   (FStar_TypeChecker_Cfg.log cfg
                      (fun uu____76891  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____76893 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____76893))
                 else
                   (let uu____76896 =
                      let uu____76901 =
                        let uu____76902 =
                          let uu____76909 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____76909
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____76902]  in
                      FStar_Syntax_Subst.open_term uu____76901 body  in
                    match uu____76896 with
                    | (bs,body1) ->
                        (FStar_TypeChecker_Cfg.log cfg
                           (fun uu____76936  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____76945 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____76945  in
                            FStar_Util.Inl
                              (let uu___2199_76961 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2199_76961.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2199_76961.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____76964  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___2204_76967 = lb  in
                             let uu____76968 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___2204_76967.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2204_76967.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____76968;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2204_76967.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2204_76967.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____76997  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___2211_77022 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps =
                                 (uu___2211_77022.FStar_TypeChecker_Cfg.steps);
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___2211_77022.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___2211_77022.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 (uu___2211_77022.FStar_TypeChecker_Cfg.delta_level);
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___2211_77022.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong = true;
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___2211_77022.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___2211_77022.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___2211_77022.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           FStar_TypeChecker_Cfg.log cfg1
                             (fun uu____77026  ->
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
               let uu____77047 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____77047 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____77083 =
                               let uu___2227_77084 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2227_77084.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2227_77084.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____77083  in
                           let uu____77085 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____77085 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____77111 =
                                   FStar_List.map (fun uu____77127  -> dummy)
                                     lbs1
                                    in
                                 let uu____77128 =
                                   let uu____77137 =
                                     FStar_List.map
                                       (fun uu____77159  -> dummy) xs1
                                      in
                                   FStar_List.append uu____77137 env  in
                                 FStar_List.append uu____77111 uu____77128
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____77185 =
                                       let uu___2241_77186 = rc  in
                                       let uu____77187 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___2241_77186.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____77187;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___2241_77186.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____77185
                                 | uu____77196 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___2246_77202 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___2246_77202.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___2246_77202.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___2246_77202.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___2246_77202.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____77212 =
                        FStar_List.map (fun uu____77228  -> dummy) lbs2  in
                      FStar_List.append uu____77212 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____77236 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____77236 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___2255_77252 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___2255_77252.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___2255_77252.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
               ->
               let uu____77286 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____77286
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____77307 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____77385  ->
                        match uu____77385 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___2271_77510 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2271_77510.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___2271_77510.FStar_Syntax_Syntax.sort)
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
               (match uu____77307 with
                | (rec_env,memos,uu____77745) ->
                    let uu____77800 =
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
                             let uu____78112 =
                               let uu____78119 =
                                 let uu____78120 =
                                   let uu____78152 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____78152, false)
                                    in
                                 Clos uu____78120  in
                               (FStar_Pervasives_Native.None, uu____78119)
                                in
                             uu____78112 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____78259  ->
                     let uu____78260 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____78260);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____78284 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____78288::uu____78289 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____78294) ->
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
                             | uu____78325 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____78341 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____78341
                              | uu____78354 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____78360 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____78384 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____78398 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____78412 =
                        let uu____78414 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____78416 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____78414 uu____78416
                         in
                      failwith uu____78412
                    else
                      (let uu____78421 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____78421)
                | uu____78422 -> norm cfg env stack t2))

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
              let uu____78431 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____78431 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____78445  ->
                        let uu____78446 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____78446);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____78459  ->
                        let uu____78460 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____78462 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____78460 uu____78462);
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
                      | (UnivArgs (us',uu____78481))::stack1 ->
                          ((let uu____78490 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____78490
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____78498 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____78498) us'
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
                      | uu____78534 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____78537 ->
                          let uu____78540 =
                            let uu____78542 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____78542
                             in
                          failwith uu____78540
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
                  let uu___2377_78570 = cfg  in
                  let uu____78571 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____78571;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___2377_78570.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___2377_78570.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___2377_78570.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___2377_78570.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___2377_78570.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___2377_78570.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___2377_78570.FStar_TypeChecker_Cfg.reifying)
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
                     (uu____78602,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____78603;
                                    FStar_Syntax_Syntax.vars = uu____78604;_},uu____78605,uu____78606))::uu____78607
                     -> ()
                 | uu____78612 ->
                     let uu____78615 =
                       let uu____78617 = stack_to_string stack  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____78617
                        in
                     failwith uu____78615);
                (let head0 = head1  in
                 let head2 = FStar_Syntax_Util.unascribe head1  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____78626  ->
                      let uu____78627 = FStar_Syntax_Print.tag_of_term head2
                         in
                      let uu____78629 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____78627
                        uu____78629);
                 (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                  let uu____78633 =
                    let uu____78634 = FStar_Syntax_Subst.compress head3  in
                    uu____78634.FStar_Syntax_Syntax.n  in
                  match uu____78633 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let ed =
                        let uu____78655 =
                          FStar_TypeChecker_Env.norm_eff_name
                            cfg.FStar_TypeChecker_Cfg.tcenv m
                           in
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv uu____78655
                         in
                      let uu____78656 = ed.FStar_Syntax_Syntax.bind_repr  in
                      (match uu____78656 with
                       | (uu____78657,bind_repr) ->
                           (match lb.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____78667 ->
                                failwith
                                  "Cannot reify a top-level let binding"
                            | FStar_Util.Inl x ->
                                let is_return e =
                                  let uu____78678 =
                                    let uu____78679 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____78679.FStar_Syntax_Syntax.n  in
                                  match uu____78678 with
                                  | FStar_Syntax_Syntax.Tm_meta
                                      (e1,FStar_Syntax_Syntax.Meta_monadic
                                       (uu____78685,uu____78686))
                                      ->
                                      let uu____78695 =
                                        let uu____78696 =
                                          FStar_Syntax_Subst.compress e1  in
                                        uu____78696.FStar_Syntax_Syntax.n  in
                                      (match uu____78695 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                            (uu____78702,msrc,uu____78704))
                                           when
                                           FStar_Syntax_Util.is_pure_effect
                                             msrc
                                           ->
                                           let uu____78713 =
                                             FStar_Syntax_Subst.compress e2
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____78713
                                       | uu____78714 ->
                                           FStar_Pervasives_Native.None)
                                  | uu____78715 ->
                                      FStar_Pervasives_Native.None
                                   in
                                let uu____78716 =
                                  is_return lb.FStar_Syntax_Syntax.lbdef  in
                                (match uu____78716 with
                                 | FStar_Pervasives_Native.Some e ->
                                     let lb1 =
                                       let uu___2449_78721 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___2449_78721.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___2449_78721.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           (uu___2449_78721.FStar_Syntax_Syntax.lbtyp);
                                         FStar_Syntax_Syntax.lbeff =
                                           FStar_Parser_Const.effect_PURE_lid;
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___2449_78721.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___2449_78721.FStar_Syntax_Syntax.lbpos)
                                       }  in
                                     let uu____78722 = FStar_List.tl stack
                                        in
                                     let uu____78723 =
                                       let uu____78724 =
                                         let uu____78731 =
                                           let uu____78732 =
                                             let uu____78746 =
                                               FStar_Syntax_Util.mk_reify
                                                 body
                                                in
                                             ((false, [lb1]), uu____78746)
                                              in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____78732
                                            in
                                         FStar_Syntax_Syntax.mk uu____78731
                                          in
                                       uu____78724
                                         FStar_Pervasives_Native.None
                                         head3.FStar_Syntax_Syntax.pos
                                        in
                                     norm cfg env uu____78722 uu____78723
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____78765 =
                                       let uu____78767 = is_return body  in
                                       match uu____78767 with
                                       | FStar_Pervasives_Native.Some
                                           {
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_bvar y;
                                             FStar_Syntax_Syntax.pos =
                                               uu____78772;
                                             FStar_Syntax_Syntax.vars =
                                               uu____78773;_}
                                           -> FStar_Syntax_Syntax.bv_eq x y
                                       | uu____78776 -> false  in
                                     if uu____78765
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
                                          let uu____78800 =
                                            let uu____78807 =
                                              let uu____78808 =
                                                let uu____78827 =
                                                  let uu____78836 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____78836]  in
                                                (uu____78827, body1,
                                                  (FStar_Pervasives_Native.Some
                                                     body_rc))
                                                 in
                                              FStar_Syntax_Syntax.Tm_abs
                                                uu____78808
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____78807
                                             in
                                          uu____78800
                                            FStar_Pervasives_Native.None
                                            body1.FStar_Syntax_Syntax.pos
                                           in
                                        let close1 = closure_as_term cfg env
                                           in
                                        let bind_inst =
                                          let uu____78878 =
                                            let uu____78879 =
                                              FStar_Syntax_Subst.compress
                                                bind_repr
                                               in
                                            uu____78879.FStar_Syntax_Syntax.n
                                             in
                                          match uu____78878 with
                                          | FStar_Syntax_Syntax.Tm_uinst
                                              (bind1,uu____78885::uu____78886::[])
                                              ->
                                              let uu____78891 =
                                                let uu____78898 =
                                                  let uu____78899 =
                                                    let uu____78906 =
                                                      let uu____78907 =
                                                        let uu____78908 =
                                                          close1
                                                            lb.FStar_Syntax_Syntax.lbtyp
                                                           in
                                                        (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.FStar_TypeChecker_Cfg.tcenv
                                                          uu____78908
                                                         in
                                                      let uu____78909 =
                                                        let uu____78912 =
                                                          let uu____78913 =
                                                            close1 t  in
                                                          (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                            cfg.FStar_TypeChecker_Cfg.tcenv
                                                            uu____78913
                                                           in
                                                        [uu____78912]  in
                                                      uu____78907 ::
                                                        uu____78909
                                                       in
                                                    (bind1, uu____78906)  in
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                    uu____78899
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____78898
                                                 in
                                              uu____78891
                                                FStar_Pervasives_Native.None
                                                rng
                                          | uu____78919 ->
                                              failwith
                                                "NIY : Reification of indexed effects"
                                           in
                                        let maybe_range_arg =
                                          let uu____78934 =
                                            FStar_Util.for_some
                                              (FStar_Syntax_Util.attr_eq
                                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                                              ed.FStar_Syntax_Syntax.eff_attrs
                                             in
                                          if uu____78934
                                          then
                                            let uu____78947 =
                                              let uu____78956 =
                                                FStar_TypeChecker_Cfg.embed_simple
                                                  FStar_Syntax_Embeddings.e_range
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____78956
                                               in
                                            let uu____78957 =
                                              let uu____78968 =
                                                let uu____78977 =
                                                  FStar_TypeChecker_Cfg.embed_simple
                                                    FStar_Syntax_Embeddings.e_range
                                                    body2.FStar_Syntax_Syntax.pos
                                                    body2.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Syntax_Syntax.as_arg
                                                  uu____78977
                                                 in
                                              [uu____78968]  in
                                            uu____78947 :: uu____78957
                                          else []  in
                                        let reified =
                                          let uu____79015 =
                                            let uu____79022 =
                                              let uu____79023 =
                                                let uu____79040 =
                                                  let uu____79051 =
                                                    let uu____79062 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        lb.FStar_Syntax_Syntax.lbtyp
                                                       in
                                                    let uu____79071 =
                                                      let uu____79082 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          t
                                                         in
                                                      [uu____79082]  in
                                                    uu____79062 ::
                                                      uu____79071
                                                     in
                                                  let uu____79115 =
                                                    let uu____79126 =
                                                      let uu____79137 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          FStar_Syntax_Syntax.tun
                                                         in
                                                      let uu____79146 =
                                                        let uu____79157 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            head4
                                                           in
                                                        let uu____79166 =
                                                          let uu____79177 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          let uu____79186 =
                                                            let uu____79197 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                body2
                                                               in
                                                            [uu____79197]  in
                                                          uu____79177 ::
                                                            uu____79186
                                                           in
                                                        uu____79157 ::
                                                          uu____79166
                                                         in
                                                      uu____79137 ::
                                                        uu____79146
                                                       in
                                                    FStar_List.append
                                                      maybe_range_arg
                                                      uu____79126
                                                     in
                                                  FStar_List.append
                                                    uu____79051 uu____79115
                                                   in
                                                (bind_inst, uu____79040)  in
                                              FStar_Syntax_Syntax.Tm_app
                                                uu____79023
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____79022
                                             in
                                          uu____79015
                                            FStar_Pervasives_Native.None rng
                                           in
                                        FStar_TypeChecker_Cfg.log cfg
                                          (fun uu____79281  ->
                                             let uu____79282 =
                                               FStar_Syntax_Print.term_to_string
                                                 head0
                                                in
                                             let uu____79284 =
                                               FStar_Syntax_Print.term_to_string
                                                 reified
                                                in
                                             FStar_Util.print2
                                               "Reified (1) <%s> to %s\n"
                                               uu____79282 uu____79284);
                                        (let uu____79287 =
                                           FStar_List.tl stack  in
                                         norm cfg env uu____79287 reified)))))
                  | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                      ((let uu____79315 = FStar_Options.defensive ()  in
                        if uu____79315
                        then
                          let is_arg_impure uu____79330 =
                            match uu____79330 with
                            | (e,q) ->
                                let uu____79344 =
                                  let uu____79345 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____79345.FStar_Syntax_Syntax.n  in
                                (match uu____79344 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____79361 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____79361
                                 | uu____79363 -> false)
                             in
                          let uu____79365 =
                            let uu____79367 =
                              let uu____79378 =
                                FStar_Syntax_Syntax.as_arg head_app  in
                              uu____79378 :: args  in
                            FStar_Util.for_some is_arg_impure uu____79367  in
                          (if uu____79365
                           then
                             let uu____79404 =
                               let uu____79410 =
                                 let uu____79412 =
                                   FStar_Syntax_Print.term_to_string head3
                                    in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____79412
                                  in
                               (FStar_Errors.Warning_Defensive, uu____79410)
                                in
                             FStar_Errors.log_issue
                               head3.FStar_Syntax_Syntax.pos uu____79404
                           else ())
                        else ());
                       (let fallback1 uu____79425 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____79429  ->
                               let uu____79430 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____79430 "");
                          (let uu____79434 = FStar_List.tl stack  in
                           let uu____79435 = FStar_Syntax_Util.mk_reify head3
                              in
                           norm cfg env uu____79434 uu____79435)
                           in
                        let fallback2 uu____79441 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____79445  ->
                               let uu____79446 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____79446 "");
                          (let uu____79450 = FStar_List.tl stack  in
                           let uu____79451 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (head3,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               head0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env uu____79450 uu____79451)
                           in
                        let uu____79456 =
                          let uu____79457 =
                            FStar_Syntax_Util.un_uinst head_app  in
                          uu____79457.FStar_Syntax_Syntax.n  in
                        match uu____79456 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____79463 =
                              let uu____79465 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____79465  in
                            if uu____79463
                            then fallback1 ()
                            else
                              (let uu____79470 =
                                 let uu____79472 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____79472  in
                               if uu____79470
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____79489 =
                                      let uu____79494 =
                                        FStar_Syntax_Util.mk_reify head_app
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____79494 args
                                       in
                                    uu____79489 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____79497 = FStar_List.tl stack  in
                                  norm cfg env uu____79497 t1))
                        | uu____79498 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____79500) ->
                      do_reify_monadic fallback cfg env stack e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____79524 = closure_as_term cfg env t'  in
                        reify_lift cfg e msrc mtgt uu____79524  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____79528  ->
                            let uu____79529 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____79529);
                       (let uu____79532 = FStar_List.tl stack  in
                        norm cfg env uu____79532 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                      let branches1 =
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun uu____79653  ->
                                match uu____79653 with
                                | (pat,wopt,tm) ->
                                    let uu____79701 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____79701)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                          head3.FStar_Syntax_Syntax.pos
                         in
                      let uu____79733 = FStar_List.tl stack  in
                      norm cfg env uu____79733 tm
                  | uu____79734 -> fallback ()))

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
              (fun uu____79748  ->
                 let uu____79749 = FStar_Ident.string_of_lid msrc  in
                 let uu____79751 = FStar_Ident.string_of_lid mtgt  in
                 let uu____79753 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____79749
                   uu____79751 uu____79753);
            (let uu____79756 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____79756
             then
               let ed =
                 let uu____79760 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____79760  in
               let uu____79761 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____79761 with
               | (uu____79762,return_repr) ->
                   let return_inst =
                     let uu____79775 =
                       let uu____79776 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____79776.FStar_Syntax_Syntax.n  in
                     match uu____79775 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____79782::[]) ->
                         let uu____79787 =
                           let uu____79794 =
                             let uu____79795 =
                               let uu____79802 =
                                 let uu____79803 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____79803]  in
                               (return_tm, uu____79802)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____79795  in
                           FStar_Syntax_Syntax.mk uu____79794  in
                         uu____79787 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____79809 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____79813 =
                     let uu____79820 =
                       let uu____79821 =
                         let uu____79838 =
                           let uu____79849 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____79858 =
                             let uu____79869 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____79869]  in
                           uu____79849 :: uu____79858  in
                         (return_inst, uu____79838)  in
                       FStar_Syntax_Syntax.Tm_app uu____79821  in
                     FStar_Syntax_Syntax.mk uu____79820  in
                   uu____79813 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____79919 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____79919 with
                | FStar_Pervasives_Native.None  ->
                    let uu____79922 =
                      let uu____79924 = FStar_Ident.text_of_lid msrc  in
                      let uu____79926 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____79924 uu____79926
                       in
                    failwith uu____79922
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____79929;
                      FStar_TypeChecker_Env.mtarget = uu____79930;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____79931;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____79953 =
                      let uu____79955 = FStar_Ident.text_of_lid msrc  in
                      let uu____79957 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____79955 uu____79957
                       in
                    failwith uu____79953
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____79960;
                      FStar_TypeChecker_Env.mtarget = uu____79961;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____79962;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____79997 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____79998 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____79997 t FStar_Syntax_Syntax.tun uu____79998))

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
                (fun uu____80068  ->
                   match uu____80068 with
                   | (a,imp) ->
                       let uu____80087 = norm cfg env [] a  in
                       (uu____80087, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____80097  ->
             let uu____80098 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____80100 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____80098 uu____80100);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____80126 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _80129  -> FStar_Pervasives_Native.Some _80129)
                     uu____80126
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2599_80130 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2599_80130.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2599_80130.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____80152 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _80155  -> FStar_Pervasives_Native.Some _80155)
                     uu____80152
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2610_80156 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2610_80156.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2610_80156.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____80201  ->
                      match uu____80201 with
                      | (a,i) ->
                          let uu____80221 = norm cfg env [] a  in
                          (uu____80221, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___600_80243  ->
                       match uu___600_80243 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____80247 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____80247
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___2627_80255 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2629_80258 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2629_80258.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2627_80255.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2627_80255.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun b  ->
        let uu____80262 = b  in
        match uu____80262 with
        | (x,imp) ->
            let x1 =
              let uu___2637_80270 = x  in
              let uu____80271 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2637_80270.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2637_80270.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____80271
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____80282 =
                    let uu____80283 = closure_as_term cfg env t  in
                    FStar_Syntax_Syntax.Meta uu____80283  in
                  FStar_Pervasives_Native.Some uu____80282
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____80294 =
          FStar_List.fold_left
            (fun uu____80328  ->
               fun b  ->
                 match uu____80328 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____80294 with | (nbs,uu____80408) -> FStar_List.rev nbs

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
            let uu____80440 =
              let uu___2662_80441 = rc  in
              let uu____80442 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2662_80441.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____80442;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2662_80441.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____80440
        | uu____80451 -> lopt

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
            (let uu____80461 = FStar_Syntax_Print.term_to_string tm  in
             let uu____80463 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____80461 uu____80463)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___601_80475  ->
      match uu___601_80475 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____80488 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____80488 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____80492 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____80492)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____80500 = norm_cb cfg  in
            reduce_primops uu____80500 cfg env tm  in
          let uu____80507 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____80507
          then tm1
          else
            (let w t =
               let uu___2690_80526 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2690_80526.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2690_80526.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____80538 =
                 let uu____80539 = FStar_Syntax_Util.unmeta t  in
                 uu____80539.FStar_Syntax_Syntax.n  in
               match uu____80538 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____80551 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____80615)::args1,(bv,uu____80618)::bs1) ->
                   let uu____80672 =
                     let uu____80673 = FStar_Syntax_Subst.compress t  in
                     uu____80673.FStar_Syntax_Syntax.n  in
                   (match uu____80672 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____80678 -> false)
               | ([],[]) -> true
               | (uu____80709,uu____80710) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____80761 = FStar_Syntax_Print.term_to_string t  in
                  let uu____80763 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____80761
                    uu____80763)
               else ();
               (let uu____80768 = FStar_Syntax_Util.head_and_args' t  in
                match uu____80768 with
                | (hd1,args) ->
                    let uu____80807 =
                      let uu____80808 = FStar_Syntax_Subst.compress hd1  in
                      uu____80808.FStar_Syntax_Syntax.n  in
                    (match uu____80807 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____80816 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____80818 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____80820 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____80816 uu____80818 uu____80820)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____80825 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____80843 = FStar_Syntax_Print.term_to_string t  in
                  let uu____80845 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____80843
                    uu____80845)
               else ();
               (let uu____80850 = FStar_Syntax_Util.is_squash t  in
                match uu____80850 with
                | FStar_Pervasives_Native.Some (uu____80861,t') ->
                    is_applied bs t'
                | uu____80873 ->
                    let uu____80882 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____80882 with
                     | FStar_Pervasives_Native.Some (uu____80893,t') ->
                         is_applied bs t'
                     | uu____80905 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____80929 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____80929 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____80936)::(q,uu____80938)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____80981 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____80983 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____80981 uu____80983)
                    else ();
                    (let uu____80988 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____80988 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____80993 =
                           let uu____80994 = FStar_Syntax_Subst.compress p
                              in
                           uu____80994.FStar_Syntax_Syntax.n  in
                         (match uu____80993 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____81005 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____81005))
                          | uu____81008 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____81011)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____81036 =
                           let uu____81037 = FStar_Syntax_Subst.compress p1
                              in
                           uu____81037.FStar_Syntax_Syntax.n  in
                         (match uu____81036 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____81048 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____81048))
                          | uu____81051 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____81055 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____81055 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____81060 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____81060 with
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
                                     let uu____81074 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____81074))
                               | uu____81077 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____81082)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____81107 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____81107 with
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
                                     let uu____81121 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____81121))
                               | uu____81124 -> FStar_Pervasives_Native.None)
                          | uu____81127 -> FStar_Pervasives_Native.None)
                     | uu____81130 -> FStar_Pervasives_Native.None))
               | uu____81133 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____81146 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____81146 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____81152)::[],uu____81153,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____81173 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____81175 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____81173
                         uu____81175)
                    else ();
                    is_quantified_const bv phi')
               | uu____81180 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____81195 =
                 let uu____81196 = FStar_Syntax_Subst.compress phi  in
                 uu____81196.FStar_Syntax_Syntax.n  in
               match uu____81195 with
               | FStar_Syntax_Syntax.Tm_match (uu____81202,br::brs) ->
                   let uu____81269 = br  in
                   (match uu____81269 with
                    | (uu____81287,uu____81288,e) ->
                        let r =
                          let uu____81310 = simp_t e  in
                          match uu____81310 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____81322 =
                                FStar_List.for_all
                                  (fun uu____81341  ->
                                     match uu____81341 with
                                     | (uu____81355,uu____81356,e') ->
                                         let uu____81370 = simp_t e'  in
                                         uu____81370 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____81322
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____81386 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____81396 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____81396
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____81434 =
                 match uu____81434 with
                 | (t1,q) ->
                     let uu____81455 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____81455 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____81487 -> (t1, q))
                  in
               let uu____81500 = FStar_Syntax_Util.head_and_args t  in
               match uu____81500 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____81580 =
                 let uu____81581 = FStar_Syntax_Util.unmeta ty  in
                 uu____81581.FStar_Syntax_Syntax.n  in
               match uu____81580 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____81586) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____81591,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____81615 -> false  in
             let simplify1 arg =
               let uu____81648 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____81648, arg)  in
             let uu____81663 = is_forall_const tm1  in
             match uu____81663 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____81669 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____81671 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____81669
                       uu____81671)
                  else ();
                  (let uu____81676 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____81676))
             | FStar_Pervasives_Native.None  ->
                 let uu____81677 =
                   let uu____81678 = FStar_Syntax_Subst.compress tm1  in
                   uu____81678.FStar_Syntax_Syntax.n  in
                 (match uu____81677 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____81682;
                              FStar_Syntax_Syntax.vars = uu____81683;_},uu____81684);
                         FStar_Syntax_Syntax.pos = uu____81685;
                         FStar_Syntax_Syntax.vars = uu____81686;_},args)
                      ->
                      let uu____81716 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____81716
                      then
                        let uu____81719 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____81719 with
                         | (FStar_Pervasives_Native.Some (true ),uu____81777)::
                             (uu____81778,(arg,uu____81780))::[] ->
                             maybe_auto_squash arg
                         | (uu____81853,(arg,uu____81855))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____81856)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____81929)::uu____81930::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____82000::(FStar_Pervasives_Native.Some (false
                                         ),uu____82001)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____82071 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____82089 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____82089
                         then
                           let uu____82092 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____82092 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____82150)::uu____82151::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____82221::(FStar_Pervasives_Native.Some (true
                                           ),uu____82222)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____82292)::(uu____82293,(arg,uu____82295))::[]
                               -> maybe_auto_squash arg
                           | (uu____82368,(arg,uu____82370))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____82371)::[]
                               -> maybe_auto_squash arg
                           | uu____82444 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____82462 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____82462
                            then
                              let uu____82465 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____82465 with
                              | uu____82523::(FStar_Pervasives_Native.Some
                                              (true ),uu____82524)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____82594)::uu____82595::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____82665)::(uu____82666,(arg,uu____82668))::[]
                                  -> maybe_auto_squash arg
                              | (uu____82741,(p,uu____82743))::(uu____82744,
                                                                (q,uu____82746))::[]
                                  ->
                                  let uu____82818 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____82818
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____82823 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____82841 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____82841
                               then
                                 let uu____82844 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____82844 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____82902)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____82903)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____82977)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____82978)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____83052)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____83053)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____83127)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____83128)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____83202,(arg,uu____83204))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____83205)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____83278)::(uu____83279,(arg,uu____83281))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____83354,(arg,uu____83356))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____83357)::[]
                                     ->
                                     let uu____83430 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____83430
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____83431)::(uu____83432,(arg,uu____83434))::[]
                                     ->
                                     let uu____83507 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____83507
                                 | (uu____83508,(p,uu____83510))::(uu____83511,
                                                                   (q,uu____83513))::[]
                                     ->
                                     let uu____83585 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____83585
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____83590 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____83608 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____83608
                                  then
                                    let uu____83611 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____83611 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____83669)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____83713)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____83757 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____83775 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____83775
                                     then
                                       match args with
                                       | (t,uu____83779)::[] ->
                                           let uu____83804 =
                                             let uu____83805 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____83805.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____83804 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____83808::[],body,uu____83810)
                                                ->
                                                let uu____83845 = simp_t body
                                                   in
                                                (match uu____83845 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____83851 -> tm1)
                                            | uu____83855 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____83857))::(t,uu____83859)::[]
                                           ->
                                           let uu____83899 =
                                             let uu____83900 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____83900.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____83899 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____83903::[],body,uu____83905)
                                                ->
                                                let uu____83940 = simp_t body
                                                   in
                                                (match uu____83940 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____83948 -> tm1)
                                            | uu____83952 -> tm1)
                                       | uu____83953 -> tm1
                                     else
                                       (let uu____83966 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____83966
                                        then
                                          match args with
                                          | (t,uu____83970)::[] ->
                                              let uu____83995 =
                                                let uu____83996 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____83996.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____83995 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____83999::[],body,uu____84001)
                                                   ->
                                                   let uu____84036 =
                                                     simp_t body  in
                                                   (match uu____84036 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____84042 -> tm1)
                                               | uu____84046 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____84048))::(t,uu____84050)::[]
                                              ->
                                              let uu____84090 =
                                                let uu____84091 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____84091.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____84090 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____84094::[],body,uu____84096)
                                                   ->
                                                   let uu____84131 =
                                                     simp_t body  in
                                                   (match uu____84131 with
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
                                                    | uu____84139 -> tm1)
                                               | uu____84143 -> tm1)
                                          | uu____84144 -> tm1
                                        else
                                          (let uu____84157 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____84157
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____84160;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____84161;_},uu____84162)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____84188;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____84189;_},uu____84190)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____84216 -> tm1
                                           else
                                             (let uu____84229 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____84229
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____84243 =
                                                    let uu____84244 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____84244.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____84243 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____84255 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     (Prims.parse_int "1")
                                                 then
                                                   let t =
                                                     let uu____84269 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____84269
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____84308 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____84308
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____84314 =
                                                         let uu____84315 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____84315.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____84314 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____84318 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____84326 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____84326
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____84335
                                                                  =
                                                                  let uu____84336
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____84336.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____84335
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____84342)
                                                                    -> hd1
                                                                | uu____84367
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____84371
                                                                =
                                                                let uu____84382
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____84382]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____84371)
                                                       | uu____84415 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____84420 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____84420 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____84440 ->
                                                     let uu____84449 =
                                                       let uu____84456 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____84456 cfg env
                                                        in
                                                     uu____84449 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____84464;
                         FStar_Syntax_Syntax.vars = uu____84465;_},args)
                      ->
                      let uu____84491 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____84491
                      then
                        let uu____84494 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____84494 with
                         | (FStar_Pervasives_Native.Some (true ),uu____84552)::
                             (uu____84553,(arg,uu____84555))::[] ->
                             maybe_auto_squash arg
                         | (uu____84628,(arg,uu____84630))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____84631)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____84704)::uu____84705::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____84775::(FStar_Pervasives_Native.Some (false
                                         ),uu____84776)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____84846 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____84864 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____84864
                         then
                           let uu____84867 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____84867 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____84925)::uu____84926::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____84996::(FStar_Pervasives_Native.Some (true
                                           ),uu____84997)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____85067)::(uu____85068,(arg,uu____85070))::[]
                               -> maybe_auto_squash arg
                           | (uu____85143,(arg,uu____85145))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____85146)::[]
                               -> maybe_auto_squash arg
                           | uu____85219 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____85237 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____85237
                            then
                              let uu____85240 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____85240 with
                              | uu____85298::(FStar_Pervasives_Native.Some
                                              (true ),uu____85299)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____85369)::uu____85370::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____85440)::(uu____85441,(arg,uu____85443))::[]
                                  -> maybe_auto_squash arg
                              | (uu____85516,(p,uu____85518))::(uu____85519,
                                                                (q,uu____85521))::[]
                                  ->
                                  let uu____85593 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____85593
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____85598 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____85616 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____85616
                               then
                                 let uu____85619 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____85619 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____85677)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____85678)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____85752)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____85753)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____85827)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____85828)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____85902)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____85903)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____85977,(arg,uu____85979))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____85980)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____86053)::(uu____86054,(arg,uu____86056))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____86129,(arg,uu____86131))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____86132)::[]
                                     ->
                                     let uu____86205 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____86205
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____86206)::(uu____86207,(arg,uu____86209))::[]
                                     ->
                                     let uu____86282 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____86282
                                 | (uu____86283,(p,uu____86285))::(uu____86286,
                                                                   (q,uu____86288))::[]
                                     ->
                                     let uu____86360 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____86360
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____86365 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____86383 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____86383
                                  then
                                    let uu____86386 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____86386 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____86444)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____86488)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____86532 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____86550 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____86550
                                     then
                                       match args with
                                       | (t,uu____86554)::[] ->
                                           let uu____86579 =
                                             let uu____86580 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____86580.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____86579 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____86583::[],body,uu____86585)
                                                ->
                                                let uu____86620 = simp_t body
                                                   in
                                                (match uu____86620 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____86626 -> tm1)
                                            | uu____86630 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____86632))::(t,uu____86634)::[]
                                           ->
                                           let uu____86674 =
                                             let uu____86675 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____86675.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____86674 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____86678::[],body,uu____86680)
                                                ->
                                                let uu____86715 = simp_t body
                                                   in
                                                (match uu____86715 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____86723 -> tm1)
                                            | uu____86727 -> tm1)
                                       | uu____86728 -> tm1
                                     else
                                       (let uu____86741 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____86741
                                        then
                                          match args with
                                          | (t,uu____86745)::[] ->
                                              let uu____86770 =
                                                let uu____86771 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____86771.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____86770 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____86774::[],body,uu____86776)
                                                   ->
                                                   let uu____86811 =
                                                     simp_t body  in
                                                   (match uu____86811 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____86817 -> tm1)
                                               | uu____86821 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____86823))::(t,uu____86825)::[]
                                              ->
                                              let uu____86865 =
                                                let uu____86866 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____86866.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____86865 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____86869::[],body,uu____86871)
                                                   ->
                                                   let uu____86906 =
                                                     simp_t body  in
                                                   (match uu____86906 with
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
                                                    | uu____86914 -> tm1)
                                               | uu____86918 -> tm1)
                                          | uu____86919 -> tm1
                                        else
                                          (let uu____86932 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____86932
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____86935;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____86936;_},uu____86937)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____86963;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____86964;_},uu____86965)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____86991 -> tm1
                                           else
                                             (let uu____87004 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____87004
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____87018 =
                                                    let uu____87019 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____87019.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____87018 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____87030 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     (Prims.parse_int "1")
                                                 then
                                                   let t =
                                                     let uu____87044 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____87044
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____87079 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____87079
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____87085 =
                                                         let uu____87086 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____87086.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____87085 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____87089 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____87097 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____87097
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____87106
                                                                  =
                                                                  let uu____87107
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____87107.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____87106
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____87113)
                                                                    -> hd1
                                                                | uu____87138
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____87142
                                                                =
                                                                let uu____87153
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____87153]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____87142)
                                                       | uu____87186 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____87191 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____87191 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____87211 ->
                                                     let uu____87220 =
                                                       let uu____87227 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____87227 cfg env
                                                        in
                                                     uu____87220 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____87240 = simp_t t  in
                      (match uu____87240 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____87249 ->
                      let uu____87272 = is_const_match tm1  in
                      (match uu____87272 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____87281 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____87291  ->
               (let uu____87293 = FStar_Syntax_Print.tag_of_term t  in
                let uu____87295 = FStar_Syntax_Print.term_to_string t  in
                let uu____87297 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____87305 =
                  let uu____87307 =
                    let uu____87310 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____87310
                     in
                  stack_to_string uu____87307  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____87293 uu____87295 uu____87297 uu____87305);
               (let uu____87335 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____87335
                then
                  let uu____87339 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____87339 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____87346 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____87348 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____87350 =
                          let uu____87352 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____87352
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____87346
                          uu____87348 uu____87350);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____87374 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack with
                | (Arg uu____87382)::uu____87383 -> true
                | uu____87393 -> false)
              in
           if uu____87374
           then
             let uu____87396 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____87396 (norm cfg env stack)
           else
             (let t1 = maybe_simplify cfg env stack t  in
              match stack with
              | [] -> t1
              | (Debug (tm,time_then))::stack1 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now ()  in
                      let uu____87410 =
                        let uu____87412 =
                          let uu____87414 =
                            FStar_Util.time_diff time_then time_now  in
                          FStar_Pervasives_Native.snd uu____87414  in
                        FStar_Util.string_of_int uu____87412  in
                      let uu____87421 = FStar_Syntax_Print.term_to_string tm
                         in
                      let uu____87423 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print3
                        "Normalized term (%s ms) %s\n\tto term %s\n"
                        uu____87410 uu____87421 uu____87423)
                   else ();
                   rebuild cfg env stack1 t1)
              | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
              | (Meta (uu____87432,m,r))::stack1 ->
                  let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
                  rebuild cfg env stack1 t2
              | (MemoLazy r)::stack1 ->
                  (set_memo cfg r (env, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu____87483  ->
                        let uu____87484 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 "\tSet memo %s\n" uu____87484);
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
                  let uu____87527 =
                    let uu___3319_87528 = FStar_Syntax_Util.abs bs1 t1 lopt1
                       in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___3319_87528.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___3319_87528.FStar_Syntax_Syntax.vars)
                    }  in
                  rebuild cfg env stack1 uu____87527
              | (Arg (Univ uu____87531,uu____87532,uu____87533))::uu____87534
                  -> failwith "Impossible"
              | (Arg (Dummy ,uu____87538,uu____87539))::uu____87540 ->
                  failwith "Impossible"
              | (UnivArgs (us,r))::stack1 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                  rebuild cfg env stack1 t2
              | (Arg
                  (Clos (env_arg,tm,uu____87556,uu____87557),aq,r))::stack1
                  when
                  let uu____87609 = head_of t1  in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____87609 ->
                  let t2 =
                    let uu____87613 =
                      let uu____87618 =
                        let uu____87619 = closure_as_term cfg env_arg tm  in
                        (uu____87619, aq)  in
                      FStar_Syntax_Syntax.extend_app t1 uu____87618  in
                    uu____87613 FStar_Pervasives_Native.None r  in
                  rebuild cfg env stack1 t2
              | (Arg (Clos (env_arg,tm,m,uu____87631),aq,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____87686  ->
                        let uu____87687 =
                          FStar_Syntax_Print.term_to_string tm  in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____87687);
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
                     (let uu____87707 = FStar_ST.op_Bang m  in
                      match uu____87707 with
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
                      | FStar_Pervasives_Native.Some (uu____87850,a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq)
                              FStar_Pervasives_Native.None r
                             in
                          rebuild cfg env_arg stack1 t2))
              | (App (env1,head1,aq,r))::stack' when should_reify cfg stack
                  ->
                  let t0 = t1  in
                  let fallback msg uu____87906 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____87911  ->
                         let uu____87912 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____87912);
                    (let t2 =
                       FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env1 stack' t2)
                     in
                  let uu____87922 =
                    let uu____87923 = FStar_Syntax_Subst.compress t1  in
                    uu____87923.FStar_Syntax_Syntax.n  in
                  (match uu____87922 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env1 stack t2 m
                         ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc,mtgt,ty))
                       ->
                       let lifted =
                         let uu____87951 = closure_as_term cfg env1 ty  in
                         reify_lift cfg t2 msrc mtgt uu____87951  in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____87955  ->
                             let uu____87956 =
                               FStar_Syntax_Print.term_to_string lifted  in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____87956);
                        (let uu____87959 = FStar_List.tl stack  in
                         norm cfg env1 uu____87959 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu____87960);
                          FStar_Syntax_Syntax.pos = uu____87961;
                          FStar_Syntax_Syntax.vars = uu____87962;_},(e,uu____87964)::[])
                       -> norm cfg env1 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____88003 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____88020 = FStar_Syntax_Util.head_and_args t1
                          in
                       (match uu____88020 with
                        | (hd1,args) ->
                            let uu____88063 =
                              let uu____88064 =
                                FStar_Syntax_Util.un_uinst hd1  in
                              uu____88064.FStar_Syntax_Syntax.n  in
                            (match uu____88063 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____88068 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv
                                    in
                                 (match uu____88068 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____88071;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____88072;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____88073;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n1;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____88075;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____88076;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____88077;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____88078;_}
                                      when (FStar_List.length args) = n1 ->
                                      norm cfg env1 stack' t1
                                  | uu____88115 -> fallback " (3)" ())
                             | uu____88119 -> fallback " (4)" ()))
                   | uu____88121 -> fallback " (2)" ())
              | (App (env1,head1,aq,r))::stack1 ->
                  let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack1 t2
              | (Match (env',branches,cfg1,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____88147  ->
                        let uu____88148 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____88148);
                   (let scrutinee_env = env  in
                    let env1 = env'  in
                    let scrutinee = t1  in
                    let norm_and_rebuild_match uu____88159 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____88164  ->
                           let uu____88165 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           let uu____88167 =
                             let uu____88169 =
                               FStar_All.pipe_right branches
                                 (FStar_List.map
                                    (fun uu____88199  ->
                                       match uu____88199 with
                                       | (p,uu____88210,uu____88211) ->
                                           FStar_Syntax_Print.pat_to_string p))
                                in
                             FStar_All.pipe_right uu____88169
                               (FStar_String.concat "\n\t")
                              in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu____88165 uu____88167);
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
                                (fun uu___602_88233  ->
                                   match uu___602_88233 with
                                   | FStar_TypeChecker_Env.InliningDelta  ->
                                       true
                                   | FStar_TypeChecker_Env.Eager_unfolding_only
                                        -> true
                                   | uu____88237 -> false))
                            in
                         let steps =
                           let uu___3487_88240 =
                             cfg1.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___3487_88240.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___3487_88240.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta = false;
                             FStar_TypeChecker_Cfg.weak =
                               (uu___3487_88240.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___3487_88240.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___3487_88240.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___3487_88240.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_only =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___3487_88240.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_tac = false;
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___3487_88240.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___3487_88240.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___3487_88240.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___3487_88240.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___3487_88240.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___3487_88240.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___3487_88240.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___3487_88240.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___3487_88240.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___3487_88240.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___3487_88240.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___3487_88240.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___3487_88240.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___3487_88240.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         let uu___3490_88247 = cfg1  in
                         {
                           FStar_TypeChecker_Cfg.steps = steps;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___3490_88247.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___3490_88247.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = new_delta;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___3490_88247.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong = true;
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___3490_88247.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets =
                             (uu___3490_88247.FStar_TypeChecker_Cfg.normalize_pure_lets);
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___3490_88247.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let norm_or_whnf env2 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env2 t2
                         else norm cfg_exclude_zeta env2 [] t2  in
                       let rec norm_pat env2 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu____88322 ->
                             (p, env2)
                         | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                             let uu____88353 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____88442  ->
                                       fun uu____88443  ->
                                         match (uu____88442, uu____88443)
                                         with
                                         | ((pats1,env3),(p1,b)) ->
                                             let uu____88593 =
                                               norm_pat env3 p1  in
                                             (match uu____88593 with
                                              | (p2,env4) ->
                                                  (((p2, b) :: pats1), env4)))
                                    ([], env2))
                                in
                             (match uu____88353 with
                              | (pats1,env3) ->
                                  ((let uu___3518_88763 = p  in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___3518_88763.FStar_Syntax_Syntax.p)
                                    }), env3))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___3522_88784 = x  in
                               let uu____88785 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3522_88784.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3522_88784.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____88785
                               }  in
                             ((let uu___3525_88799 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3525_88799.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___3529_88810 = x  in
                               let uu____88811 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3529_88810.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3529_88810.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____88811
                               }  in
                             ((let uu___3532_88825 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3532_88825.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                             let x1 =
                               let uu___3538_88841 = x  in
                               let uu____88842 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3538_88841.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3538_88841.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____88842
                               }  in
                             let t3 = norm_or_whnf env2 t2  in
                             ((let uu___3542_88857 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___3542_88857.FStar_Syntax_Syntax.p)
                               }), env2)
                          in
                       let branches1 =
                         match env1 with
                         | [] when whnf -> branches
                         | uu____88901 ->
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun branch1  ->
                                     let uu____88931 =
                                       FStar_Syntax_Subst.open_branch branch1
                                        in
                                     match uu____88931 with
                                     | (p,wopt,e) ->
                                         let uu____88951 = norm_pat env1 p
                                            in
                                         (match uu____88951 with
                                          | (p1,env2) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu____89006 =
                                                      norm_or_whnf env2 w  in
                                                    FStar_Pervasives_Native.Some
                                                      uu____89006
                                                 in
                                              let e1 = norm_or_whnf env2 e
                                                 in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1))))
                          in
                       let scrutinee1 =
                         let uu____89023 =
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
                         if uu____89023
                         then
                           norm
                             (let uu___3561_89030 = cfg1  in
                              {
                                FStar_TypeChecker_Cfg.steps =
                                  (let uu___3563_89033 =
                                     cfg1.FStar_TypeChecker_Cfg.steps  in
                                   {
                                     FStar_TypeChecker_Cfg.beta =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.beta);
                                     FStar_TypeChecker_Cfg.iota =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.iota);
                                     FStar_TypeChecker_Cfg.zeta =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.zeta);
                                     FStar_TypeChecker_Cfg.weak =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.weak);
                                     FStar_TypeChecker_Cfg.hnf =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.hnf);
                                     FStar_TypeChecker_Cfg.primops =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.primops);
                                     FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                       =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                     FStar_TypeChecker_Cfg.unfold_until =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.unfold_until);
                                     FStar_TypeChecker_Cfg.unfold_only =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.unfold_only);
                                     FStar_TypeChecker_Cfg.unfold_fully =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.unfold_fully);
                                     FStar_TypeChecker_Cfg.unfold_attr =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.unfold_attr);
                                     FStar_TypeChecker_Cfg.unfold_tac =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.unfold_tac);
                                     FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                       =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                     FStar_TypeChecker_Cfg.simplify =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.simplify);
                                     FStar_TypeChecker_Cfg.erase_universes =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.erase_universes);
                                     FStar_TypeChecker_Cfg.allow_unbound_universes
                                       =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                     FStar_TypeChecker_Cfg.reify_ =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.reify_);
                                     FStar_TypeChecker_Cfg.compress_uvars =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.compress_uvars);
                                     FStar_TypeChecker_Cfg.no_full_norm =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.no_full_norm);
                                     FStar_TypeChecker_Cfg.check_no_uvars =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.check_no_uvars);
                                     FStar_TypeChecker_Cfg.unmeta =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.unmeta);
                                     FStar_TypeChecker_Cfg.unascribe =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.unascribe);
                                     FStar_TypeChecker_Cfg.in_full_norm_request
                                       =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.in_full_norm_request);
                                     FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                       = false;
                                     FStar_TypeChecker_Cfg.nbe_step =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.nbe_step);
                                     FStar_TypeChecker_Cfg.for_extraction =
                                       (uu___3563_89033.FStar_TypeChecker_Cfg.for_extraction)
                                   });
                                FStar_TypeChecker_Cfg.tcenv =
                                  (uu___3561_89030.FStar_TypeChecker_Cfg.tcenv);
                                FStar_TypeChecker_Cfg.debug =
                                  (uu___3561_89030.FStar_TypeChecker_Cfg.debug);
                                FStar_TypeChecker_Cfg.delta_level =
                                  (uu___3561_89030.FStar_TypeChecker_Cfg.delta_level);
                                FStar_TypeChecker_Cfg.primitive_steps =
                                  (uu___3561_89030.FStar_TypeChecker_Cfg.primitive_steps);
                                FStar_TypeChecker_Cfg.strong =
                                  (uu___3561_89030.FStar_TypeChecker_Cfg.strong);
                                FStar_TypeChecker_Cfg.memoize_lazy =
                                  (uu___3561_89030.FStar_TypeChecker_Cfg.memoize_lazy);
                                FStar_TypeChecker_Cfg.normalize_pure_lets =
                                  (uu___3561_89030.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                FStar_TypeChecker_Cfg.reifying =
                                  (uu___3561_89030.FStar_TypeChecker_Cfg.reifying)
                              }) scrutinee_env [] scrutinee
                         else scrutinee  in
                       let uu____89037 =
                         mk
                           (FStar_Syntax_Syntax.Tm_match
                              (scrutinee1, branches1)) r
                          in
                       rebuild cfg1 env1 stack1 uu____89037)
                       in
                    let rec is_cons head1 =
                      let uu____89063 =
                        let uu____89064 = FStar_Syntax_Subst.compress head1
                           in
                        uu____89064.FStar_Syntax_Syntax.n  in
                      match uu____89063 with
                      | FStar_Syntax_Syntax.Tm_uinst (h,uu____89069) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____89074 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____89076;
                            FStar_Syntax_Syntax.fv_delta = uu____89077;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor );_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____89079;
                            FStar_Syntax_Syntax.fv_delta = uu____89080;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____89081);_}
                          -> true
                      | uu____89089 -> false  in
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
                      let uu____89258 =
                        FStar_Syntax_Util.head_and_args scrutinee2  in
                      match uu____89258 with
                      | (head1,args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu____89355 ->
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
                                | uu____89397 ->
                                    let uu____89398 =
                                      let uu____89400 = is_cons head1  in
                                      Prims.op_Negation uu____89400  in
                                    FStar_Util.Inr uu____89398)
                           | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                               let uu____89429 =
                                 let uu____89430 =
                                   FStar_Syntax_Util.un_uinst head1  in
                                 uu____89430.FStar_Syntax_Syntax.n  in
                               (match uu____89429 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____89449 ->
                                    let uu____89450 =
                                      let uu____89452 = is_cons head1  in
                                      Prims.op_Negation uu____89452  in
                                    FStar_Util.Inr uu____89450))
                    
                    and matches_args out a p =
                      match (a, p) with
                      | ([],[]) -> FStar_Util.Inl out
                      | ((t2,uu____89543)::rest_a,(p1,uu____89546)::rest_p)
                          ->
                          let uu____89605 = matches_pat t2 p1  in
                          (match uu____89605 with
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu____89658 -> FStar_Util.Inr false
                     in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1,wopt,b)::rest ->
                          let uu____89781 = matches_pat scrutinee1 p1  in
                          (match uu____89781 with
                           | FStar_Util.Inr (false ) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true ) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu____89827  ->
                                     let uu____89828 =
                                       FStar_Syntax_Print.pat_to_string p1
                                        in
                                     let uu____89830 =
                                       let uu____89832 =
                                         FStar_List.map
                                           (fun uu____89844  ->
                                              match uu____89844 with
                                              | (uu____89850,t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s
                                          in
                                       FStar_All.pipe_right uu____89832
                                         (FStar_String.concat "; ")
                                        in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu____89828 uu____89830);
                                (let env0 = env1  in
                                 let env2 =
                                   FStar_List.fold_left
                                     (fun env2  ->
                                        fun uu____89886  ->
                                          match uu____89886 with
                                          | (bv,t2) ->
                                              let uu____89909 =
                                                let uu____89916 =
                                                  let uu____89919 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____89919
                                                   in
                                                let uu____89920 =
                                                  let uu____89921 =
                                                    let uu____89953 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2))
                                                       in
                                                    ([], t2, uu____89953,
                                                      false)
                                                     in
                                                  Clos uu____89921  in
                                                (uu____89916, uu____89920)
                                                 in
                                              uu____89909 :: env2) env1 s
                                    in
                                 let uu____90068 =
                                   guard_when_clause wopt b rest  in
                                 norm cfg1 env2 stack1 uu____90068)))
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
            (fun uu____90101  ->
               let uu____90102 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____90102);
          (let uu____90105 = is_nbe_request s  in
           if uu____90105
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____90111  ->
                   let uu____90112 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____90112);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____90118  ->
                   let uu____90119 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____90119);
              (let uu____90122 =
                 FStar_Util.record_time (fun uu____90129  -> nbe_eval c s t)
                  in
               match uu____90122 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____90138  ->
                         let uu____90139 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____90141 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____90139 uu____90141);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____90149  ->
                   let uu____90150 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____90150);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____90156  ->
                   let uu____90157 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____90157);
              (let uu____90160 =
                 FStar_Util.record_time (fun uu____90167  -> norm c [] [] t)
                  in
               match uu____90160 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____90182  ->
                         let uu____90183 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____90185 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____90183 uu____90185);
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
        let uu____90220 = FStar_TypeChecker_Cfg.config s e  in
        norm_comp uu____90220 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____90238 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____90238 [] u
  
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
        let uu____90264 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____90264  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____90271 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___3719_90290 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3719_90290.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3719_90290.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name
              cfg.FStar_TypeChecker_Cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____90297 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____90297
          then
            let ct1 =
              let uu____90301 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____90301 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____90308 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____90308
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3729_90315 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3729_90315.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3729_90315.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3729_90315.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev
                      cfg.FStar_TypeChecker_Cfg.tcenv c
                     in
                  let uu___3733_90317 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3733_90317.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3733_90317.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3733_90317.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3733_90317.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3736_90318 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3736_90318.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3736_90318.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____90321 -> c
  
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
        let uu____90341 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____90341  in
      let uu____90348 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____90348
      then
        let uu____90351 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____90351 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____90357  ->
                 let uu____90358 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____90358)
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
          (fun uu___3752_90375  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___3751_90378 ->
            ((let uu____90380 =
                let uu____90386 =
                  let uu____90388 = FStar_Util.message_of_exn uu___3751_90378
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____90388
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____90386)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____90380);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          (fun uu___3762_90407  ->
             match () with
             | () ->
                 let uu____90408 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____90408 [] c) ()
        with
        | uu___3761_90417 ->
            ((let uu____90419 =
                let uu____90425 =
                  let uu____90427 = FStar_Util.message_of_exn uu___3761_90417
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____90427
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____90425)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____90419);
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
                   let uu____90476 =
                     let uu____90477 =
                       let uu____90484 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____90484)  in
                     FStar_Syntax_Syntax.Tm_refine uu____90477  in
                   mk uu____90476 t01.FStar_Syntax_Syntax.pos
               | uu____90489 -> t2)
          | uu____90490 -> t2  in
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
        let uu____90584 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____90584 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____90621 ->
                 let uu____90630 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____90630 with
                  | (actuals,uu____90640,uu____90641) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____90661 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____90661 with
                         | (binders,args) ->
                             let uu____90672 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____90672
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
      | uu____90687 ->
          let uu____90688 = FStar_Syntax_Util.head_and_args t  in
          (match uu____90688 with
           | (head1,args) ->
               let uu____90731 =
                 let uu____90732 = FStar_Syntax_Subst.compress head1  in
                 uu____90732.FStar_Syntax_Syntax.n  in
               (match uu____90731 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____90753 =
                      let uu____90768 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____90768  in
                    (match uu____90753 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____90808 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___3832_90816 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3832_90816.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3832_90816.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3832_90816.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3832_90816.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3832_90816.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3832_90816.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3832_90816.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3832_90816.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3832_90816.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___3832_90816.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3832_90816.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3832_90816.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3832_90816.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3832_90816.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3832_90816.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3832_90816.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3832_90816.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3832_90816.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3832_90816.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3832_90816.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3832_90816.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3832_90816.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3832_90816.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3832_90816.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3832_90816.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3832_90816.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3832_90816.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3832_90816.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3832_90816.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3832_90816.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3832_90816.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3832_90816.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3832_90816.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3832_90816.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3832_90816.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___3832_90816.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3832_90816.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3832_90816.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3832_90816.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3832_90816.FStar_TypeChecker_Env.nbe)
                                 }) t
                               in
                            match uu____90808 with
                            | (uu____90819,ty,uu____90821) ->
                                eta_expand_with_type env t ty))
                | uu____90822 ->
                    let uu____90823 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___3839_90831 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3839_90831.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3839_90831.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3839_90831.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3839_90831.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3839_90831.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3839_90831.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3839_90831.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3839_90831.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3839_90831.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___3839_90831.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3839_90831.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3839_90831.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3839_90831.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3839_90831.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3839_90831.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3839_90831.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3839_90831.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3839_90831.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3839_90831.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3839_90831.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3839_90831.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3839_90831.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3839_90831.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3839_90831.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3839_90831.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3839_90831.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3839_90831.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3839_90831.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3839_90831.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3839_90831.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3839_90831.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3839_90831.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3839_90831.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3839_90831.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3839_90831.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___3839_90831.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3839_90831.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3839_90831.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3839_90831.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3839_90831.FStar_TypeChecker_Env.nbe)
                         }) t
                       in
                    (match uu____90823 with
                     | (uu____90834,ty,uu____90836) ->
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
      let uu___3851_90918 = x  in
      let uu____90919 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3851_90918.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3851_90918.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____90919
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____90922 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____90946 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____90947 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____90948 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____90949 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____90956 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____90957 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____90958 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3877_90992 = rc  in
          let uu____90993 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____91002 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3877_90992.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____90993;
            FStar_Syntax_Syntax.residual_flags = uu____91002
          }  in
        let uu____91005 =
          let uu____91006 =
            let uu____91025 = elim_delayed_subst_binders bs  in
            let uu____91034 = elim_delayed_subst_term t2  in
            let uu____91037 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____91025, uu____91034, uu____91037)  in
          FStar_Syntax_Syntax.Tm_abs uu____91006  in
        mk1 uu____91005
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____91074 =
          let uu____91075 =
            let uu____91090 = elim_delayed_subst_binders bs  in
            let uu____91099 = elim_delayed_subst_comp c  in
            (uu____91090, uu____91099)  in
          FStar_Syntax_Syntax.Tm_arrow uu____91075  in
        mk1 uu____91074
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____91118 =
          let uu____91119 =
            let uu____91126 = elim_bv bv  in
            let uu____91127 = elim_delayed_subst_term phi  in
            (uu____91126, uu____91127)  in
          FStar_Syntax_Syntax.Tm_refine uu____91119  in
        mk1 uu____91118
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____91158 =
          let uu____91159 =
            let uu____91176 = elim_delayed_subst_term t2  in
            let uu____91179 = elim_delayed_subst_args args  in
            (uu____91176, uu____91179)  in
          FStar_Syntax_Syntax.Tm_app uu____91159  in
        mk1 uu____91158
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3899_91251 = p  in
              let uu____91252 =
                let uu____91253 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____91253  in
              {
                FStar_Syntax_Syntax.v = uu____91252;
                FStar_Syntax_Syntax.p =
                  (uu___3899_91251.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3903_91255 = p  in
              let uu____91256 =
                let uu____91257 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____91257  in
              {
                FStar_Syntax_Syntax.v = uu____91256;
                FStar_Syntax_Syntax.p =
                  (uu___3903_91255.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3909_91264 = p  in
              let uu____91265 =
                let uu____91266 =
                  let uu____91273 = elim_bv x  in
                  let uu____91274 = elim_delayed_subst_term t0  in
                  (uu____91273, uu____91274)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____91266  in
              {
                FStar_Syntax_Syntax.v = uu____91265;
                FStar_Syntax_Syntax.p =
                  (uu___3909_91264.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3915_91299 = p  in
              let uu____91300 =
                let uu____91301 =
                  let uu____91315 =
                    FStar_List.map
                      (fun uu____91341  ->
                         match uu____91341 with
                         | (x,b) ->
                             let uu____91358 = elim_pat x  in
                             (uu____91358, b)) pats
                     in
                  (fv, uu____91315)  in
                FStar_Syntax_Syntax.Pat_cons uu____91301  in
              {
                FStar_Syntax_Syntax.v = uu____91300;
                FStar_Syntax_Syntax.p =
                  (uu___3915_91299.FStar_Syntax_Syntax.p)
              }
          | uu____91373 -> p  in
        let elim_branch uu____91397 =
          match uu____91397 with
          | (pat,wopt,t3) ->
              let uu____91423 = elim_pat pat  in
              let uu____91426 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____91429 = elim_delayed_subst_term t3  in
              (uu____91423, uu____91426, uu____91429)
           in
        let uu____91434 =
          let uu____91435 =
            let uu____91458 = elim_delayed_subst_term t2  in
            let uu____91461 = FStar_List.map elim_branch branches  in
            (uu____91458, uu____91461)  in
          FStar_Syntax_Syntax.Tm_match uu____91435  in
        mk1 uu____91434
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____91592 =
          match uu____91592 with
          | (tc,topt) ->
              let uu____91627 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____91637 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____91637
                | FStar_Util.Inr c ->
                    let uu____91639 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____91639
                 in
              let uu____91640 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____91627, uu____91640)
           in
        let uu____91649 =
          let uu____91650 =
            let uu____91677 = elim_delayed_subst_term t2  in
            let uu____91680 = elim_ascription a  in
            (uu____91677, uu____91680, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____91650  in
        mk1 uu____91649
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3945_91743 = lb  in
          let uu____91744 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____91747 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3945_91743.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3945_91743.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____91744;
            FStar_Syntax_Syntax.lbeff =
              (uu___3945_91743.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____91747;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3945_91743.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3945_91743.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____91750 =
          let uu____91751 =
            let uu____91765 =
              let uu____91773 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____91773)  in
            let uu____91785 = elim_delayed_subst_term t2  in
            (uu____91765, uu____91785)  in
          FStar_Syntax_Syntax.Tm_let uu____91751  in
        mk1 uu____91750
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____91830 =
          let uu____91831 =
            let uu____91838 = elim_delayed_subst_term tm  in
            (uu____91838, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____91831  in
        mk1 uu____91830
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____91849 =
          let uu____91850 =
            let uu____91857 = elim_delayed_subst_term t2  in
            let uu____91860 = elim_delayed_subst_meta md  in
            (uu____91857, uu____91860)  in
          FStar_Syntax_Syntax.Tm_meta uu____91850  in
        mk1 uu____91849

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
      (fun uu___603_91869  ->
         match uu___603_91869 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____91873 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____91873
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
        let uu____91896 =
          let uu____91897 =
            let uu____91906 = elim_delayed_subst_term t  in
            (uu____91906, uopt)  in
          FStar_Syntax_Syntax.Total uu____91897  in
        mk1 uu____91896
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____91923 =
          let uu____91924 =
            let uu____91933 = elim_delayed_subst_term t  in
            (uu____91933, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____91924  in
        mk1 uu____91923
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3978_91942 = ct  in
          let uu____91943 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____91946 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____91957 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3978_91942.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3978_91942.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____91943;
            FStar_Syntax_Syntax.effect_args = uu____91946;
            FStar_Syntax_Syntax.flags = uu____91957
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___604_91960  ->
    match uu___604_91960 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____91974 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____91974
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____92013 =
          let uu____92020 = elim_delayed_subst_term t  in (m, uu____92020)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____92013
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____92032 =
          let uu____92041 = elim_delayed_subst_term t  in
          (m1, m2, uu____92041)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____92032
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
      (fun uu____92074  ->
         match uu____92074 with
         | (t,q) ->
             let uu____92093 = elim_delayed_subst_term t  in (uu____92093, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____92121  ->
         match uu____92121 with
         | (x,q) ->
             let uu____92140 =
               let uu___4002_92141 = x  in
               let uu____92142 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___4002_92141.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___4002_92141.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____92142
               }  in
             (uu____92140, q)) bs

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
            | (uu____92250,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____92282,FStar_Util.Inl t) ->
                let uu____92304 =
                  let uu____92311 =
                    let uu____92312 =
                      let uu____92327 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____92327)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____92312  in
                  FStar_Syntax_Syntax.mk uu____92311  in
                uu____92304 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____92343 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____92343 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____92375 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____92448 ->
                    let uu____92449 =
                      let uu____92458 =
                        let uu____92459 = FStar_Syntax_Subst.compress t4  in
                        uu____92459.FStar_Syntax_Syntax.n  in
                      (uu____92458, tc)  in
                    (match uu____92449 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____92488) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____92535) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____92580,FStar_Util.Inl uu____92581) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____92612 -> failwith "Impossible")
                 in
              (match uu____92375 with
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
          let uu____92751 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____92751 with
          | (univ_names1,binders1,tc) ->
              let uu____92825 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____92825)
  
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
          let uu____92879 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____92879 with
          | (univ_names1,binders1,tc) ->
              let uu____92953 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____92953)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____92995 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____92995 with
           | (univ_names1,binders1,typ1) ->
               let uu___4085_93035 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4085_93035.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4085_93035.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4085_93035.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4085_93035.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___4091_93050 = s  in
          let uu____93051 =
            let uu____93052 =
              let uu____93061 = FStar_List.map (elim_uvars env) sigs  in
              (uu____93061, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____93052  in
          {
            FStar_Syntax_Syntax.sigel = uu____93051;
            FStar_Syntax_Syntax.sigrng =
              (uu___4091_93050.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___4091_93050.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___4091_93050.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___4091_93050.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____93080 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____93080 with
           | (univ_names1,uu____93104,typ1) ->
               let uu___4105_93126 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4105_93126.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4105_93126.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4105_93126.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4105_93126.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____93133 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____93133 with
           | (univ_names1,uu____93157,typ1) ->
               let uu___4116_93179 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4116_93179.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4116_93179.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4116_93179.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4116_93179.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____93209 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____93209 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____93234 =
                            let uu____93235 =
                              let uu____93236 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____93236  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____93235
                             in
                          elim_delayed_subst_term uu____93234  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___4132_93239 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___4132_93239.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___4132_93239.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___4132_93239.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___4132_93239.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___4135_93240 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___4135_93240.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___4135_93240.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___4135_93240.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___4135_93240.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___4139_93247 = s  in
          let uu____93248 =
            let uu____93249 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____93249  in
          {
            FStar_Syntax_Syntax.sigel = uu____93248;
            FStar_Syntax_Syntax.sigrng =
              (uu___4139_93247.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___4139_93247.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___4139_93247.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___4139_93247.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____93253 = elim_uvars_aux_t env us [] t  in
          (match uu____93253 with
           | (us1,uu____93277,t1) ->
               let uu___4150_93299 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4150_93299.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4150_93299.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4150_93299.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4150_93299.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____93300 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____93303 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____93303 with
           | (univs1,binders,signature) ->
               let uu____93343 =
                 let uu____93348 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____93348 with
                 | (univs_opening,univs2) ->
                     let uu____93371 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____93371)
                  in
               (match uu____93343 with
                | (univs_opening,univs_closing) ->
                    let uu____93374 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____93380 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____93381 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____93380, uu____93381)  in
                    (match uu____93374 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____93407 =
                           match uu____93407 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____93425 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____93425 with
                                | (us1,t1) ->
                                    let uu____93436 =
                                      let uu____93445 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____93456 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____93445, uu____93456)  in
                                    (match uu____93436 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____93485 =
                                           let uu____93494 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____93505 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____93494, uu____93505)  in
                                         (match uu____93485 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____93535 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____93535
                                                 in
                                              let uu____93536 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____93536 with
                                               | (uu____93563,uu____93564,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____93587 =
                                                       let uu____93588 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____93588
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____93587
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____93597 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____93597 with
                           | (uu____93616,uu____93617,t1) -> t1  in
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
                             | uu____93693 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____93720 =
                               let uu____93721 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____93721.FStar_Syntax_Syntax.n  in
                             match uu____93720 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____93780 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____93814 =
                               let uu____93815 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____93815.FStar_Syntax_Syntax.n  in
                             match uu____93814 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____93838) ->
                                 let uu____93863 = destruct_action_body body
                                    in
                                 (match uu____93863 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____93912 ->
                                 let uu____93913 = destruct_action_body t  in
                                 (match uu____93913 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____93968 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____93968 with
                           | (action_univs,t) ->
                               let uu____93977 = destruct_action_typ_templ t
                                  in
                               (match uu____93977 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___4236_94024 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___4236_94024.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___4236_94024.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___4239_94026 = ed  in
                           let uu____94027 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____94028 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____94029 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____94030 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____94031 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____94032 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____94033 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____94034 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____94035 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____94036 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____94037 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____94038 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____94039 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____94040 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___4239_94026.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___4239_94026.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____94027;
                             FStar_Syntax_Syntax.bind_wp = uu____94028;
                             FStar_Syntax_Syntax.if_then_else = uu____94029;
                             FStar_Syntax_Syntax.ite_wp = uu____94030;
                             FStar_Syntax_Syntax.stronger = uu____94031;
                             FStar_Syntax_Syntax.close_wp = uu____94032;
                             FStar_Syntax_Syntax.assert_p = uu____94033;
                             FStar_Syntax_Syntax.assume_p = uu____94034;
                             FStar_Syntax_Syntax.null_wp = uu____94035;
                             FStar_Syntax_Syntax.trivial = uu____94036;
                             FStar_Syntax_Syntax.repr = uu____94037;
                             FStar_Syntax_Syntax.return_repr = uu____94038;
                             FStar_Syntax_Syntax.bind_repr = uu____94039;
                             FStar_Syntax_Syntax.actions = uu____94040;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___4239_94026.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___4242_94043 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___4242_94043.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___4242_94043.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___4242_94043.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___4242_94043.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___605_94064 =
            match uu___605_94064 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____94095 = elim_uvars_aux_t env us [] t  in
                (match uu____94095 with
                 | (us1,uu____94127,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___4257_94158 = sub_eff  in
            let uu____94159 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____94162 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___4257_94158.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___4257_94158.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____94159;
              FStar_Syntax_Syntax.lift = uu____94162
            }  in
          let uu___4260_94165 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___4260_94165.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___4260_94165.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___4260_94165.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___4260_94165.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____94175 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____94175 with
           | (univ_names1,binders1,comp1) ->
               let uu___4273_94215 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4273_94215.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4273_94215.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4273_94215.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4273_94215.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____94218 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____94219 -> s
  
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
        let uu____94268 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____94268 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____94290 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____94290 with
             | (uu____94297,head_def) ->
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
      let uu____94303 = FStar_Syntax_Util.head_and_args t  in
      match uu____94303 with
      | (head1,args) ->
          let uu____94348 =
            let uu____94349 = FStar_Syntax_Subst.compress head1  in
            uu____94349.FStar_Syntax_Syntax.n  in
          (match uu____94348 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____94356;
                  FStar_Syntax_Syntax.vars = uu____94357;_},us)
               -> aux fv us args
           | uu____94363 -> FStar_Pervasives_Native.None)
  