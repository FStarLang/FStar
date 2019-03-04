open Prims
let cases :
  'Auu____64069 'Auu____64070 .
    ('Auu____64069 -> 'Auu____64070) ->
      'Auu____64070 ->
        'Auu____64069 FStar_Pervasives_Native.option -> 'Auu____64070
  =
  fun f  ->
    fun d  ->
      fun uu___585_64090  ->
        match uu___585_64090 with
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
    match projectee with | Clos _0 -> true | uu____64188 -> false
  
let (__proj__Clos__item___0 :
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
      Prims.list * FStar_Syntax_Syntax.term * ((FStar_Syntax_Syntax.binder
      FStar_Pervasives_Native.option * closure) Prims.list *
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool))
  = fun projectee  -> match projectee with | Clos _0 -> _0 
let (uu___is_Univ : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____64301 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____64320 -> false
  
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
    match projectee with | Arg _0 -> true | uu____64500 -> false
  
let (__proj__Arg__item___0 :
  stack_elt -> (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)) =
  fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____64544 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range))
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____64588 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo) =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____64667 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env * branches * FStar_TypeChecker_Cfg.cfg * FStar_Range.range))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____64723 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * env *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
      FStar_Range.range))
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____64787 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Range.range))
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____64837 -> false
  
let (__proj__Meta__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.metadata * FStar_Range.range)) =
  fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____64883 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding *
      FStar_Range.range))
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____64927 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> FStar_TypeChecker_Cfg.cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____64951 -> false
  
let (__proj__Debug__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.term * FStar_Util.time)) =
  fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____64981 = FStar_Syntax_Util.head_and_args' t  in
    match uu____64981 with | (hd1,uu____64997) -> hd1
  
let mk :
  'Auu____65025 .
    'Auu____65025 ->
      FStar_Range.range -> 'Auu____65025 FStar_Syntax_Syntax.syntax
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
          let uu____65090 = FStar_ST.op_Bang r  in
          match uu____65090 with
          | FStar_Pervasives_Native.Some uu____65138 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____65215 =
      FStar_List.map
        (fun uu____65231  ->
           match uu____65231 with
           | (bopt,c) ->
               let uu____65245 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____65250 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____65245 uu____65250) env
       in
    FStar_All.pipe_right uu____65215 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___586_65258  ->
    match uu___586_65258 with
    | Clos (env,t,uu____65262,uu____65263) ->
        let uu____65310 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____65320 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____65310 uu____65320
    | Univ uu____65323 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___587_65332  ->
    match uu___587_65332 with
    | Arg (c,uu____65335,uu____65336) ->
        let uu____65337 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____65337
    | MemoLazy uu____65340 -> "MemoLazy"
    | Abs (uu____65348,bs,uu____65350,uu____65351,uu____65352) ->
        let uu____65357 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____65357
    | UnivArgs uu____65368 -> "UnivArgs"
    | Match uu____65376 -> "Match"
    | App (uu____65386,t,uu____65388,uu____65389) ->
        let uu____65390 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____65390
    | Meta (uu____65393,m,uu____65395) -> "Meta"
    | Let uu____65397 -> "Let"
    | Cfg uu____65407 -> "Cfg"
    | Debug (t,uu____65410) ->
        let uu____65411 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____65411
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____65425 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____65425 (FStar_String.concat "; ")
  
let is_empty : 'Auu____65440 . 'Auu____65440 Prims.list -> Prims.bool =
  fun uu___588_65448  ->
    match uu___588_65448 with | [] -> true | uu____65452 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        (fun uu___700_65485  ->
           match () with
           | () ->
               let uu____65486 =
                 FStar_List.nth env x.FStar_Syntax_Syntax.index  in
               FStar_Pervasives_Native.snd uu____65486) ()
      with
      | uu___699_65503 ->
          let uu____65504 =
            let uu____65506 = FStar_Syntax_Print.db_to_string x  in
            let uu____65508 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____65506
              uu____65508
             in
          failwith uu____65504
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____65519 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____65519
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____65526 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____65526
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____65533 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____65533
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
          let uu____65571 =
            FStar_List.fold_left
              (fun uu____65597  ->
                 fun u1  ->
                   match uu____65597 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____65622 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____65622 with
                        | (k_u,n1) ->
                            let uu____65640 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____65640
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____65571 with
          | (uu____65661,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 (fun uu___734_65687  ->
                    match () with
                    | () ->
                        let uu____65690 =
                          let uu____65691 = FStar_List.nth env x  in
                          FStar_Pervasives_Native.snd uu____65691  in
                        (match uu____65690 with
                         | Univ u3 ->
                             ((let uu____65710 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      cfg.FStar_TypeChecker_Cfg.tcenv)
                                   (FStar_Options.Other "univ_norm")
                                  in
                               if uu____65710
                               then
                                 let uu____65715 =
                                   FStar_Syntax_Print.univ_to_string u3  in
                                 FStar_Util.print1
                                   "Univ (in norm_universe): %s\n"
                                   uu____65715
                               else ());
                              aux u3)
                         | Dummy  -> [u2]
                         | uu____65720 ->
                             let uu____65721 =
                               let uu____65723 = FStar_Util.string_of_int x
                                  in
                               FStar_Util.format1
                                 "Impossible: universe variable u@%s bound to a term"
                                 uu____65723
                                in
                             failwith uu____65721)) ()
               with
               | uu____65733 ->
                   if
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else
                     (let uu____65739 =
                        let uu____65741 = FStar_Util.string_of_int x  in
                        FStar_String.op_Hat "Universe variable not found: u@"
                          uu____65741
                         in
                      failwith uu____65739))
          | FStar_Syntax_Syntax.U_unif uu____65746 when
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____65755 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____65764 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____65771 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____65771 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____65788 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____65788 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____65799 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____65809 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____65809 with
                                  | (uu____65816,m) -> n1 <= m))
                           in
                        if uu____65799 then rest1 else us1
                    | uu____65825 -> us1)
               | uu____65831 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____65835 = aux u3  in
              FStar_List.map
                (fun _65838  -> FStar_Syntax_Syntax.U_succ _65838)
                uu____65835
           in
        if
          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____65842 = aux u  in
           match uu____65842 with
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
            (fun uu____66011  ->
               let uu____66012 = FStar_Syntax_Print.tag_of_term t  in
               let uu____66014 = env_to_string env  in
               let uu____66016 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____66012 uu____66014 uu____66016);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____66029 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____66032 ->
                    let uu____66055 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____66055
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____66056 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____66057 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____66058 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____66059 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____66084 ->
                           let uu____66097 =
                             let uu____66099 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____66101 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____66099 uu____66101
                              in
                           failwith uu____66097
                       | uu____66106 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___589_66142  ->
                                         match uu___589_66142 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____66149 =
                                               let uu____66156 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____66156)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____66149
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___828_66168 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___828_66168.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___828_66168.FStar_Syntax_Syntax.sort)
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
                                              | uu____66174 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____66177 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___837_66182 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___837_66182.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___837_66182.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____66203 =
                        let uu____66204 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____66204  in
                      mk uu____66203 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____66212 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____66212  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____66214 = lookup_bvar env x  in
                    (match uu____66214 with
                     | Univ uu____66217 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___853_66222 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___853_66222.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___853_66222.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____66228,uu____66229) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____66320  ->
                              fun stack1  ->
                                match uu____66320 with
                                | (a,aq) ->
                                    let uu____66332 =
                                      let uu____66333 =
                                        let uu____66340 =
                                          let uu____66341 =
                                            let uu____66373 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____66373, false)  in
                                          Clos uu____66341  in
                                        (uu____66340, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____66333  in
                                    uu____66332 :: stack1) args)
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
                    let uu____66563 = close_binders cfg env bs  in
                    (match uu____66563 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,uu____66613) when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    ->
                    inline_closure_env cfg env stack
                      x.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____66624 =
                      let uu____66637 =
                        let uu____66646 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____66646]  in
                      close_binders cfg env uu____66637  in
                    (match uu____66624 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____66691 =
                             let uu____66692 =
                               let uu____66699 =
                                 let uu____66700 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____66700
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____66699, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____66692  in
                           mk uu____66691 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____66799 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____66799
                      | FStar_Util.Inr c ->
                          let uu____66813 = close_comp cfg env c  in
                          FStar_Util.Inr uu____66813
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____66832 =
                        let uu____66833 =
                          let uu____66860 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____66860, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____66833  in
                      mk uu____66832 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____66906 =
                            let uu____66907 =
                              let uu____66914 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____66914, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____66907  in
                          mk uu____66906 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____66969  -> dummy :: env1) env
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
                    let uu____66990 =
                      let uu____67001 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____67001
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____67023 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___945_67039 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___945_67039.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___945_67039.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____67023))
                       in
                    (match uu____66990 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___950_67057 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___950_67057.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___950_67057.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___950_67057.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___950_67057.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____67074,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____67140  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____67157 =
                          FStar_Syntax_Syntax.is_top_level lbs  in
                        if uu____67157
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____67172  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____67196 =
                          FStar_Syntax_Syntax.is_top_level lbs  in
                        if uu____67196
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___973_67207 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___973_67207.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___973_67207.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___976_67208 = lb  in
                      let uu____67209 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___976_67208.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___976_67208.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____67209;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___976_67208.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___976_67208.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____67241  -> fun env1  -> dummy :: env1)
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
            (fun uu____67333  ->
               let uu____67334 = FStar_Syntax_Print.tag_of_term t  in
               let uu____67336 = env_to_string env  in
               let uu____67338 = stack_to_string stack  in
               let uu____67340 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____67334 uu____67336 uu____67338 uu____67340);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____67347,uu____67348),aq,r))::stack1
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
               let uu____67429 = close_binders cfg env' bs  in
               (match uu____67429 with
                | (bs1,uu____67445) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____67465 =
                      let uu___1034_67468 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___1034_67468.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___1034_67468.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____67465)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____67524 =
                 match uu____67524 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____67639 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____67670 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____67759  ->
                                     fun uu____67760  ->
                                       match (uu____67759, uu____67760) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____67910 = norm_pat env4 p1
                                              in
                                           (match uu____67910 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____67670 with
                            | (pats1,env4) ->
                                ((let uu___1071_68080 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___1071_68080.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___1075_68101 = x  in
                             let uu____68102 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1075_68101.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1075_68101.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____68102
                             }  in
                           ((let uu___1078_68116 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___1078_68116.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___1082_68127 = x  in
                             let uu____68128 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1082_68127.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1082_68127.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____68128
                             }  in
                           ((let uu___1085_68142 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___1085_68142.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___1091_68158 = x  in
                             let uu____68159 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1091_68158.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1091_68158.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____68159
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___1095_68176 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___1095_68176.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____68181 = norm_pat env2 pat  in
                     (match uu____68181 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____68250 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____68250
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____68269 =
                   let uu____68270 =
                     let uu____68293 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____68293)  in
                   FStar_Syntax_Syntax.Tm_match uu____68270  in
                 mk uu____68269 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____68408 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____68517  ->
                                       match uu____68517 with
                                       | (a,q) ->
                                           let uu____68544 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____68544, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____68408
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____68557 =
                       let uu____68564 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____68564)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____68557
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____68576 =
                       let uu____68585 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____68585)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____68576
                 | uu____68590 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____68596 -> failwith "Impossible: unexpected stack element")

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
            let uu____68612 =
              let uu____68613 = inline_closure_env cfg env [] t  in
              FStar_Syntax_Syntax.Meta uu____68613  in
            FStar_Pervasives_Native.Some uu____68612
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
        let uu____68630 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____68714  ->
                  fun uu____68715  ->
                    match (uu____68714, uu____68715) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___1148_68855 = b  in
                          let uu____68856 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1148_68855.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1148_68855.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____68856
                          }  in
                        let imp1 = close_imp cfg env1 imp  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp1) :: out))) (env, []))
           in
        match uu____68630 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____68998 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____69011 = inline_closure_env cfg env [] t  in
                 let uu____69012 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____69011 uu____69012
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____69025 = inline_closure_env cfg env [] t  in
                 let uu____69026 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____69025 uu____69026
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____69080  ->
                           match uu____69080 with
                           | (a,q) ->
                               let uu____69101 =
                                 inline_closure_env cfg env [] a  in
                               (uu____69101, q)))
                    in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___590_69118  ->
                           match uu___590_69118 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____69122 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____69122
                           | f -> f))
                    in
                 let uu____69126 =
                   let uu___1181_69127 = c1  in
                   let uu____69128 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____69128;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___1181_69127.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____69126)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___591_69138  ->
            match uu___591_69138 with
            | FStar_Syntax_Syntax.DECREASES uu____69140 -> false
            | uu____69144 -> true))

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
                   (fun uu___592_69163  ->
                      match uu___592_69163 with
                      | FStar_Syntax_Syntax.DECREASES uu____69165 -> false
                      | uu____69169 -> true))
               in
            let rc1 =
              let uu___1198_69172 = rc  in
              let uu____69173 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___1198_69172.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____69173;
                FStar_Syntax_Syntax.residual_flags = flags
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____69182 -> lopt

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
    let uu____69252 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____69252 with
    | FStar_Pervasives_Native.Some e ->
        let uu____69291 = FStar_Syntax_Embeddings.unembed e t  in
        uu____69291 true FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____69315 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv * 'Auu____69315)
        FStar_Pervasives_Native.option * closure) Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____69377  ->
           fun subst1  ->
             match uu____69377 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____69418,uu____69419)) ->
                      let uu____69480 = b  in
                      (match uu____69480 with
                       | (bv,uu____69488) ->
                           let uu____69489 =
                             let uu____69491 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____69491  in
                           if uu____69489
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____69499 = unembed_binder term1  in
                              match uu____69499 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____69506 =
                                      let uu___1233_69507 = bv  in
                                      let uu____69508 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___1233_69507.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___1233_69507.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____69508
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____69506
                                     in
                                  let b_for_x =
                                    let uu____69514 =
                                      let uu____69521 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____69521)
                                       in
                                    FStar_Syntax_Syntax.NT uu____69514  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___593_69537  ->
                                         match uu___593_69537 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____69539,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____69541;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____69542;_})
                                             ->
                                             let uu____69547 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____69547
                                         | uu____69549 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____69551 -> subst1)) env []
  
let reduce_primops :
  'Auu____69574 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'Auu____69574)
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
            (let uu____69628 = FStar_Syntax_Util.head_and_args tm  in
             match uu____69628 with
             | (head1,args) ->
                 let uu____69673 =
                   let uu____69674 = FStar_Syntax_Util.un_uinst head1  in
                   uu____69674.FStar_Syntax_Syntax.n  in
                 (match uu____69673 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____69680 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                      (match uu____69680 with
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
                                (fun uu____69709  ->
                                   let uu____69710 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name
                                      in
                                   let uu____69712 =
                                     FStar_Util.string_of_int l  in
                                   let uu____69720 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____69710 uu____69712 uu____69720);
                              tm)
                           else
                             (let uu____69725 =
                                if l = prim_step.FStar_TypeChecker_Cfg.arity
                                then (args, [])
                                else
                                  FStar_List.splitAt
                                    prim_step.FStar_TypeChecker_Cfg.arity
                                    args
                                 in
                              match uu____69725 with
                              | (args_1,args_2) ->
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____69815  ->
                                        let uu____69816 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____69816);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____69821  ->
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
                                           (fun uu____69837  ->
                                              let uu____69838 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____69838);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____69846  ->
                                              let uu____69847 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____69849 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____69847 uu____69849);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____69852 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____69856  ->
                                 let uu____69857 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____69857);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____69863  ->
                            let uu____69864 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____69864);
                       (match args with
                        | (a1,uu____69870)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____69895 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____69909  ->
                            let uu____69910 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____69910);
                       (match args with
                        | (t,uu____69916)::(r,uu____69918)::[] ->
                            let uu____69959 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____69959 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____69965 -> tm))
                  | uu____69976 -> tm))
  
let reduce_equality :
  'Auu____69988 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'Auu____69988)
          FStar_Pervasives_Native.option * closure) Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun tm  ->
        reduce_primops norm_cb
          (let uu___1321_70041 = cfg  in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___1323_70044 = FStar_TypeChecker_Cfg.default_steps  in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.nbe_step);
                  FStar_TypeChecker_Cfg.for_extraction =
                    (uu___1323_70044.FStar_TypeChecker_Cfg.for_extraction)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___1321_70041.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___1321_70041.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___1321_70041.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___1321_70041.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___1321_70041.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___1321_70041.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___1321_70041.FStar_TypeChecker_Cfg.reifying)
           }) tm
  
type norm_request_t =
  | Norm_request_none 
  | Norm_request_ready 
  | Norm_request_requires_rejig 
let (uu___is_Norm_request_none : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_none  -> true | uu____70055 -> false
  
let (uu___is_Norm_request_ready : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_ready  -> true | uu____70066 -> false
  
let (uu___is_Norm_request_requires_rejig : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Norm_request_requires_rejig  -> true
    | uu____70077 -> false
  
let (is_norm_request :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.args -> norm_request_t) =
  fun hd1  ->
    fun args  ->
      let aux min_args =
        let uu____70098 = FStar_All.pipe_right args FStar_List.length  in
        FStar_All.pipe_right uu____70098
          (fun n1  ->
             if n1 < min_args
             then Norm_request_none
             else
               if n1 = min_args
               then Norm_request_ready
               else Norm_request_requires_rejig)
         in
      let uu____70130 =
        let uu____70131 = FStar_Syntax_Util.un_uinst hd1  in
        uu____70131.FStar_Syntax_Syntax.n  in
      match uu____70130 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          -> aux (Prims.parse_int "2")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          aux (Prims.parse_int "1")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          aux (Prims.parse_int "3")
      | uu____70140 -> Norm_request_none
  
let (should_consider_norm_requests : FStar_TypeChecker_Cfg.cfg -> Prims.bool)
  =
  fun cfg  ->
    (Prims.op_Negation
       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
      &&
      (let uu____70149 =
         FStar_Ident.lid_equals
           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
           FStar_Parser_Const.prims_lid
          in
       Prims.op_Negation uu____70149)
  
let (rejig_norm_request :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term)
  =
  fun hd1  ->
    fun args  ->
      let uu____70162 =
        let uu____70163 = FStar_Syntax_Util.un_uinst hd1  in
        uu____70163.FStar_Syntax_Syntax.n  in
      match uu____70162 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          ->
          (match args with
           | t1::t2::rest when
               (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____70221 = FStar_Syntax_Util.mk_app hd1 [t1; t2]  in
               FStar_Syntax_Util.mk_app uu____70221 rest
           | uu____70248 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize_term")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          (match args with
           | t::rest when (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____70288 = FStar_Syntax_Util.mk_app hd1 [t]  in
               FStar_Syntax_Util.mk_app uu____70288 rest
           | uu____70307 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          (match args with
           | t1::t2::t3::rest when
               (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____70381 = FStar_Syntax_Util.mk_app hd1 [t1; t2; t3]
                  in
               FStar_Syntax_Util.mk_app uu____70381 rest
           | uu____70416 ->
               failwith "Impossible! invalid rejig_norm_request for norm")
      | uu____70418 ->
          let uu____70419 =
            let uu____70421 = FStar_Syntax_Print.term_to_string hd1  in
            FStar_String.op_Hat
              "Impossible! invalid rejig_norm_request for: %s" uu____70421
             in
          failwith uu____70419
  
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s  ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
  
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___594_70442  ->
    match uu___594_70442 with
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
        let uu____70449 =
          let uu____70452 =
            let uu____70453 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            FStar_TypeChecker_Env.UnfoldOnly uu____70453  in
          [uu____70452]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____70449
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____70461 =
          let uu____70464 =
            let uu____70465 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            FStar_TypeChecker_Env.UnfoldFully uu____70465  in
          [uu____70464]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____70461
    | FStar_Syntax_Embeddings.UnfoldAttr names1 ->
        let uu____70473 =
          let uu____70476 =
            let uu____70477 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            FStar_TypeChecker_Env.UnfoldAttr uu____70477  in
          [uu____70476]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____70473
    | FStar_Syntax_Embeddings.NBE  -> [FStar_TypeChecker_Env.NBE]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  = fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____70502 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term * 'Auu____70502) Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list * FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____70553 =
            let uu____70558 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____70558 s  in
          match uu____70553 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____70574 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____70574
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
        | uu____70609::(tm,uu____70611)::[] ->
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
        | (tm,uu____70640)::[] ->
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
        | (steps,uu____70661)::uu____70662::(tm,uu____70664)::[] ->
            let add_exclude s z =
              let uu____70702 =
                FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s  in
              if uu____70702
              then s
              else (FStar_TypeChecker_Env.Exclude z) :: s  in
            let uu____70709 =
              let uu____70714 = full_norm steps  in parse_steps uu____70714
               in
            (match uu____70709 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = FStar_TypeChecker_Env.Beta :: s  in
                 let s2 = add_exclude s1 FStar_TypeChecker_Env.Zeta  in
                 let s3 = add_exclude s2 FStar_TypeChecker_Env.Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____70753 -> FStar_Pervasives_Native.None
  
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun s  ->
      fun tm  ->
        let delta_level =
          let uu____70785 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___595_70792  ->
                    match uu___595_70792 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____70794 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____70796 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____70800 -> true
                    | uu____70804 -> false))
             in
          if uu____70785
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta]  in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____70814  ->
             let uu____70815 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____70815);
        (let tm_norm =
           let uu____70819 =
             let uu____70834 = FStar_TypeChecker_Cfg.cfg_env cfg  in
             uu____70834.FStar_TypeChecker_Env.nbe  in
           uu____70819 s cfg.FStar_TypeChecker_Cfg.tcenv tm  in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____70838  ->
              let uu____70839 = FStar_Syntax_Print.term_to_string tm_norm  in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____70839);
         tm_norm)
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___596_70850  ->
    match uu___596_70850 with
    | (App
        (uu____70854,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____70855;
                       FStar_Syntax_Syntax.vars = uu____70856;_},uu____70857,uu____70858))::uu____70859
        -> true
    | uu____70865 -> false
  
let firstn :
  'Auu____70876 .
    Prims.int ->
      'Auu____70876 Prims.list ->
        ('Auu____70876 Prims.list * 'Auu____70876 Prims.list)
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack  ->
      let rec drop_irrel uu___597_70933 =
        match uu___597_70933 with
        | (MemoLazy uu____70938)::s -> drop_irrel s
        | (UnivArgs uu____70948)::s -> drop_irrel s
        | s -> s  in
      let uu____70961 = drop_irrel stack  in
      match uu____70961 with
      | (App
          (uu____70965,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____70966;
                         FStar_Syntax_Syntax.vars = uu____70967;_},uu____70968,uu____70969))::uu____70970
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____70975 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____71004) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____71014) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____71035  ->
                  match uu____71035 with
                  | (a,uu____71046) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____71057 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____71082 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____71084 -> false
    | FStar_Syntax_Syntax.Tm_type uu____71098 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____71100 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____71102 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____71104 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____71106 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____71109 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____71117 -> false
    | FStar_Syntax_Syntax.Tm_let uu____71125 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____71140 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____71160 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____71176 -> true
    | FStar_Syntax_Syntax.Tm_match uu____71184 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____71256  ->
                   match uu____71256 with
                   | (a,uu____71267) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____71278) ->
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
                     (fun uu____71410  ->
                        match uu____71410 with
                        | (a,uu____71421) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____71430,uu____71431,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____71437,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____71443 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____71453 -> false
            | FStar_Syntax_Syntax.Meta_named uu____71455 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____71466 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____71477 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Should_unfold_fully  -> true
    | uu____71488 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Should_unfold_reify  -> true
    | uu____71499 -> false
  
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
            let uu____71532 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo
               in
            match uu____71532 with
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
              (fun uu____71731  ->
                 fun uu____71732  ->
                   match (uu____71731, uu____71732) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____71838 =
            match uu____71838 with
            | (x,y,z) ->
                let uu____71858 = FStar_Util.string_of_bool x  in
                let uu____71860 = FStar_Util.string_of_bool y  in
                let uu____71862 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____71858 uu____71860
                  uu____71862
             in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg  in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____71890  ->
                    let uu____71891 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____71893 = FStar_Util.string_of_bool b  in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____71891 uu____71893);
               if b then reif else no)
            else
              if
                (let uu____71908 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                 FStar_Option.isSome uu____71908)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____71913  ->
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
                          ((is_rec,uu____71948),uu____71949);
                        FStar_Syntax_Syntax.sigrng = uu____71950;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____71952;
                        FStar_Syntax_Syntax.sigattrs = uu____71953;_},uu____71954),uu____71955),uu____71956,uu____71957,uu____71958)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____72065  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____72067,uu____72068,uu____72069,uu____72070) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____72137  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____72140),uu____72141);
                        FStar_Syntax_Syntax.sigrng = uu____72142;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____72144;
                        FStar_Syntax_Syntax.sigattrs = uu____72145;_},uu____72146),uu____72147),uu____72148,uu____72149,uu____72150)
                     when
                     is_rec &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____72257  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____72259,FStar_Pervasives_Native.Some
                    uu____72260,uu____72261,uu____72262) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____72330  ->
                           let uu____72331 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____72331);
                      (let uu____72334 =
                         let uu____72346 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____72372 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____72372
                            in
                         let uu____72384 =
                           let uu____72396 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____72422 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____72422
                              in
                           let uu____72438 =
                             let uu____72450 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____72476 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____72476
                                in
                             [uu____72450]  in
                           uu____72396 :: uu____72438  in
                         uu____72346 :: uu____72384  in
                       comb_or uu____72334))
                 | (uu____72524,uu____72525,FStar_Pervasives_Native.Some
                    uu____72526,uu____72527) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____72595  ->
                           let uu____72596 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____72596);
                      (let uu____72599 =
                         let uu____72611 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____72637 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____72637
                            in
                         let uu____72649 =
                           let uu____72661 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____72687 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____72687
                              in
                           let uu____72703 =
                             let uu____72715 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____72741 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____72741
                                in
                             [uu____72715]  in
                           uu____72661 :: uu____72703  in
                         uu____72611 :: uu____72649  in
                       comb_or uu____72599))
                 | (uu____72789,uu____72790,uu____72791,FStar_Pervasives_Native.Some
                    uu____72792) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____72860  ->
                           let uu____72861 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____72861);
                      (let uu____72864 =
                         let uu____72876 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____72902 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____72902
                            in
                         let uu____72914 =
                           let uu____72926 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____72952 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____72952
                              in
                           let uu____72968 =
                             let uu____72980 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____73006 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____73006
                                in
                             [uu____72980]  in
                           uu____72926 :: uu____72968  in
                         uu____72876 :: uu____72914  in
                       comb_or uu____72864))
                 | uu____73054 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____73100  ->
                           let uu____73101 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____73103 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____73105 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level
                              in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____73101 uu____73103 uu____73105);
                      (let uu____73108 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___598_73114  ->
                                 match uu___598_73114 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.InliningDelta  ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____73120 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv
                                        in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____73120 l))
                          in
                       FStar_All.pipe_left yesno uu____73108)))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____73136  ->
               let uu____73137 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____73139 =
                 let uu____73141 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____73141  in
               let uu____73142 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____73137 uu____73139 uu____73142);
          (match res with
           | (false ,uu____73145,uu____73146) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____73171 ->
               let uu____73181 =
                 let uu____73183 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____73183
                  in
               FStar_All.pipe_left failwith uu____73181)
  
let decide_unfolding :
  'Auu____73202 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'Auu____73202 ->
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
                    let uu___1740_73271 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___1742_73274 =
                           cfg.FStar_TypeChecker_Cfg.steps  in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1742_73274.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1742_73274.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1742_73274.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1742_73274.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1742_73274.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1742_73274.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1742_73274.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___1742_73274.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1742_73274.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1742_73274.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1742_73274.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1742_73274.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1742_73274.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1742_73274.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1742_73274.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1742_73274.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1742_73274.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1742_73274.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___1742_73274.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1742_73274.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1742_73274.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1742_73274.FStar_TypeChecker_Cfg.for_extraction)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1740_73271.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1740_73271.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___1740_73271.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1740_73271.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1740_73271.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1740_73271.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1740_73271.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1740_73271.FStar_TypeChecker_Cfg.reifying)
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
                        let uu____73336 = push1 e t  in (UnivArgs (us, r)) ::
                          uu____73336
                    | h::t -> e :: h :: t  in
                  let ref =
                    let uu____73348 =
                      let uu____73355 =
                        let uu____73356 =
                          let uu____73357 = FStar_Syntax_Syntax.lid_of_fv fv
                             in
                          FStar_Const.Const_reflect uu____73357  in
                        FStar_Syntax_Syntax.Tm_constant uu____73356  in
                      FStar_Syntax_Syntax.mk uu____73355  in
                    uu____73348 FStar_Pervasives_Native.None
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
    let uu____73426 =
      let uu____73427 = FStar_Syntax_Subst.compress t  in
      uu____73427.FStar_Syntax_Syntax.n  in
    match uu____73426 with
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____73458 =
          let uu____73459 = FStar_Syntax_Util.un_uinst hd1  in
          uu____73459.FStar_Syntax_Syntax.n  in
        (match uu____73458 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStar_List.length args) = (Prims.parse_int "3"))
             ->
             let f =
               let uu____73476 =
                 let uu____73483 =
                   let uu____73494 = FStar_All.pipe_right args FStar_List.tl
                      in
                   FStar_All.pipe_right uu____73494 FStar_List.tl  in
                 FStar_All.pipe_right uu____73483 FStar_List.hd  in
               FStar_All.pipe_right uu____73476 FStar_Pervasives_Native.fst
                in
             FStar_Pervasives_Native.Some f
         | uu____73593 -> FStar_Pervasives_Native.None)
    | uu____73594 -> FStar_Pervasives_Native.None
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____73873 ->
                   let uu____73896 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____73896
               | uu____73899 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____73909  ->
               let uu____73910 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____73912 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____73914 = FStar_Syntax_Print.term_to_string t1  in
               let uu____73916 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____73924 =
                 let uu____73926 =
                   let uu____73929 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____73929
                    in
                 stack_to_string uu____73926  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____73910 uu____73912 uu____73914 uu____73916 uu____73924);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____73957  ->
               let uu____73958 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____73958);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____73964  ->
                     let uu____73965 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____73965);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____73968 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____73972  ->
                     let uu____73973 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____73973);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____73976 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____73980  ->
                     let uu____73981 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____73981);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____73984 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____73988  ->
                     let uu____73989 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____73989);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____73992;
                 FStar_Syntax_Syntax.fv_delta = uu____73993;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____73997  ->
                     let uu____73998 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____73998);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____74001;
                 FStar_Syntax_Syntax.fv_delta = uu____74002;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____74003);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____74013  ->
                     let uu____74014 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____74014);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid
                  in
               let uu____74020 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
               (match uu____74020 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level _74023) when
                    _74023 = (Prims.parse_int "0") ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____74027  ->
                          let uu____74028 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____74028);
                     rebuild cfg env stack t1)
                | uu____74031 ->
                    let uu____74034 =
                      decide_unfolding cfg env stack
                        t1.FStar_Syntax_Syntax.pos fv qninfo
                       in
                    (match uu____74034 with
                     | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                         do_unfold_fv cfg1 env stack1 t1 qninfo fv
                     | FStar_Pervasives_Native.None  ->
                         rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_quoted uu____74061 ->
               let uu____74068 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____74068
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____74096 = is_norm_request hd1 args  in
                  uu____74096 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu____74102 = rejig_norm_request hd1 args  in
                 norm cfg env stack uu____74102))
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____74130 = is_norm_request hd1 args  in
                  uu____74130 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___1850_74137 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1852_74140 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1852_74140.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1852_74140.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1852_74140.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___1852_74140.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1852_74140.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1852_74140.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1852_74140.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1852_74140.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1852_74140.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1852_74140.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1852_74140.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1852_74140.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1852_74140.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1852_74140.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1852_74140.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1852_74140.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1852_74140.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1852_74140.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1852_74140.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1852_74140.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1852_74140.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1852_74140.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1852_74140.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1850_74137.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1850_74137.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1850_74137.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1850_74137.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1850_74137.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1850_74137.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____74147 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____74147 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____74183  ->
                                 fun stack1  ->
                                   match uu____74183 with
                                   | (a,aq) ->
                                       let uu____74195 =
                                         let uu____74196 =
                                           let uu____74203 =
                                             let uu____74204 =
                                               let uu____74236 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____74236, false)
                                                in
                                             Clos uu____74204  in
                                           (uu____74203, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____74196  in
                                       uu____74195 :: stack1) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____74326  ->
                            let uu____74327 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____74327);
                       norm cfg env stack1 hd1))
                 | FStar_Pervasives_Native.Some (s,tm) when is_nbe_request s
                     ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____74354 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting NBE request on %s ... \n" uu____74354)
                      else ();
                      (let tm' = closure_as_term cfg env tm  in
                       let start = FStar_Util.now ()  in
                       let tm_norm = nbe_eval cfg s tm'  in
                       let fin = FStar_Util.now ()  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         (let uu____74365 =
                            let uu____74367 =
                              let uu____74369 =
                                FStar_Util.time_diff start fin  in
                              FStar_Pervasives_Native.snd uu____74369  in
                            FStar_Util.string_of_int uu____74367  in
                          let uu____74376 =
                            FStar_Syntax_Print.term_to_string tm'  in
                          let uu____74378 =
                            FStar_Syntax_Print.term_to_string tm_norm  in
                          FStar_Util.print3 "NBE'd (%s ms) %s\n\tto %s\n"
                            uu____74365 uu____74376 uu____74378)
                       else ();
                       norm cfg env stack tm_norm))
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____74397 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting norm request on %s ... \n" uu____74397)
                      else ();
                      (let delta_level =
                         let uu____74405 =
                           FStar_All.pipe_right s
                             (FStar_Util.for_some
                                (fun uu___599_74412  ->
                                   match uu___599_74412 with
                                   | FStar_TypeChecker_Env.UnfoldUntil
                                       uu____74414 -> true
                                   | FStar_TypeChecker_Env.UnfoldOnly
                                       uu____74416 -> true
                                   | FStar_TypeChecker_Env.UnfoldFully
                                       uu____74420 -> true
                                   | uu____74424 -> false))
                            in
                         if uu____74405
                         then
                           [FStar_TypeChecker_Env.Unfold
                              FStar_Syntax_Syntax.delta_constant]
                         else [FStar_TypeChecker_Env.NoDelta]  in
                       let cfg'1 =
                         let uu___1893_74432 = cfg  in
                         let uu____74433 =
                           let uu___1895_74434 =
                             FStar_TypeChecker_Cfg.to_fsteps s  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.unfold_only);
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               true;
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___1895_74434.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         {
                           FStar_TypeChecker_Cfg.steps = uu____74433;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___1893_74432.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___1893_74432.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = delta_level;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___1893_74432.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong =
                             (uu___1893_74432.FStar_TypeChecker_Cfg.strong);
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___1893_74432.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___1893_74432.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let stack' =
                         let tail1 = (Cfg cfg) :: stack  in
                         if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           let uu____74442 =
                             let uu____74443 =
                               let uu____74448 = FStar_Util.now ()  in
                               (t1, uu____74448)  in
                             Debug uu____74443  in
                           uu____74442 :: tail1
                         else tail1  in
                       norm cfg'1 env stack' tm))))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____74453 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____74453
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____74464 =
                      let uu____74471 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____74471, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____74464  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____74480 = lookup_bvar env x  in
               (match uu____74480 with
                | Univ uu____74481 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                    then
                      let uu____74535 = FStar_ST.op_Bang r  in
                      (match uu____74535 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____74653  ->
                                 let uu____74654 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____74656 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____74654
                                   uu____74656);
                            (let uu____74659 = maybe_weakly_reduced t'  in
                             if uu____74659
                             then
                               match stack with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____74662 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____74739)::uu____74740 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____74751,uu____74752))::stack_rest ->
                    (match c with
                     | Univ uu____74756 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____74765 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____74795  ->
                                    let uu____74796 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____74796);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____74832  ->
                                    let uu____74833 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____74833);
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
                       (fun uu____74903  ->
                          let uu____74904 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____74904);
                     norm cfg env stack1 t1)
                | (Match uu____74907)::uu____74908 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____74923 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____74923 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____74959  -> dummy :: env1) env)
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
                                          let uu____75003 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____75003)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_75011 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_75011.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_75011.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____75012 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____75018  ->
                                 let uu____75019 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____75019);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_75034 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_75034.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_75034.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_75034.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_75034.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_75034.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_75034.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_75034.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_75034.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____75038)::uu____75039 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____75050 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____75050 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____75086  -> dummy :: env1) env)
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
                                          let uu____75130 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____75130)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_75138 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_75138.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_75138.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____75139 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____75145  ->
                                 let uu____75146 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____75146);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_75161 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_75161.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_75161.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_75161.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_75161.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_75161.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_75161.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_75161.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_75161.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____75165)::uu____75166 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____75179 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____75179 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____75215  -> dummy :: env1) env)
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
                                          let uu____75259 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____75259)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_75267 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_75267.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_75267.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____75268 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____75274  ->
                                 let uu____75275 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____75275);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_75290 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_75290.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_75290.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_75290.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_75290.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_75290.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_75290.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_75290.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_75290.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____75294)::uu____75295 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____75310 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____75310 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____75346  -> dummy :: env1) env)
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
                                          let uu____75390 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____75390)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_75398 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_75398.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_75398.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____75399 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____75405  ->
                                 let uu____75406 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____75406);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_75421 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_75421.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_75421.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_75421.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_75421.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_75421.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_75421.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_75421.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_75421.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____75425)::uu____75426 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____75441 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____75441 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____75477  -> dummy :: env1) env)
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
                                          let uu____75521 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____75521)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_75529 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_75529.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_75529.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____75530 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____75536  ->
                                 let uu____75537 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____75537);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_75552 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_75552.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_75552.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_75552.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_75552.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_75552.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_75552.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_75552.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_75552.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____75556)::uu____75557 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____75576 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____75576 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____75612  -> dummy :: env1) env)
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
                                          let uu____75656 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____75656)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_75664 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_75664.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_75664.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____75665 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____75671  ->
                                 let uu____75672 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____75672);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_75687 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_75687.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_75687.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_75687.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_75687.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_75687.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_75687.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_75687.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_75687.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____75695 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____75695 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____75731  -> dummy :: env1) env)
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
                                          let uu____75775 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____75775)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_75783 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_75783.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_75783.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____75784 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____75790  ->
                                 let uu____75791 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____75791);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_75806 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_75806.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_75806.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_75806.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_75806.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_75806.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_75806.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_75806.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_75806.FStar_TypeChecker_Cfg.reifying)
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
                      (fun uu____75850  ->
                         fun stack1  ->
                           match uu____75850 with
                           | (a,aq) ->
                               let uu____75862 =
                                 let uu____75863 =
                                   let uu____75870 =
                                     let uu____75871 =
                                       let uu____75903 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____75903, false)  in
                                     Clos uu____75871  in
                                   (uu____75870, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____75863  in
                               uu____75862 :: stack1) args)
                  in
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____75993  ->
                     let uu____75994 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____75994);
                norm cfg env stack1 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,uu____76008) when
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
                             ((let uu___2047_76053 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2047_76053.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2047_76053.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____76054 ->
                      let uu____76069 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____76069)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____76073 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____76073 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____76104 =
                          let uu____76105 =
                            let uu____76112 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___2056_76118 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2056_76118.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___2056_76118.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____76112)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____76105  in
                        mk uu____76104 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____76142 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____76142
               else
                 (let uu____76145 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____76145 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____76153 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____76179  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____76153 c1  in
                      let t2 =
                        let uu____76203 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____76203 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____76316)::uu____76317 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____76330  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____76332)::uu____76333 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____76344  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____76346,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____76347;
                                   FStar_Syntax_Syntax.vars = uu____76348;_},uu____76349,uu____76350))::uu____76351
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____76358  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____76360)::uu____76361 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____76372  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____76374 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____76377  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____76382  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____76408 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____76408
                         | FStar_Util.Inr c ->
                             let uu____76422 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____76422
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____76445 =
                               let uu____76446 =
                                 let uu____76473 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____76473, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____76446
                                in
                             mk uu____76445 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____76508 ->
                           let uu____76509 =
                             let uu____76510 =
                               let uu____76511 =
                                 let uu____76538 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____76538, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____76511
                                in
                             mk uu____76510 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____76509))))
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
                   let uu___2135_76616 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___2137_76619 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___2137_76619.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___2135_76616.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___2135_76616.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___2135_76616.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___2135_76616.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___2135_76616.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___2135_76616.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___2135_76616.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___2135_76616.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____76660 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____76660 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___2150_76680 = cfg  in
                               let uu____76681 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2150_76680.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____76681;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2150_76680.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2150_76680.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2150_76680.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___2150_76680.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2150_76680.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2150_76680.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2150_76680.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____76688 =
                                 let uu____76689 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____76689  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____76688
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___2157_76692 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___2157_76692.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2157_76692.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2157_76692.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2157_76692.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____76693 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____76693
           | FStar_Syntax_Syntax.Tm_let
               ((uu____76706,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____76707;
                               FStar_Syntax_Syntax.lbunivs = uu____76708;
                               FStar_Syntax_Syntax.lbtyp = uu____76709;
                               FStar_Syntax_Syntax.lbeff = uu____76710;
                               FStar_Syntax_Syntax.lbdef = uu____76711;
                               FStar_Syntax_Syntax.lbattrs = uu____76712;
                               FStar_Syntax_Syntax.lbpos = uu____76713;_}::uu____76714),uu____76715)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name
                   cfg.FStar_TypeChecker_Cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____76761 =
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
               if uu____76761
               then
                 let binder =
                   let uu____76765 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____76765  in
                 let env1 =
                   let uu____76775 =
                     let uu____76782 =
                       let uu____76783 =
                         let uu____76815 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____76815,
                           false)
                          in
                       Clos uu____76783  in
                     ((FStar_Pervasives_Native.Some binder), uu____76782)  in
                   uu____76775 :: env  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____76912  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                 then
                   (FStar_TypeChecker_Cfg.log cfg
                      (fun uu____76919  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____76921 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____76921))
                 else
                   (let uu____76924 =
                      let uu____76929 =
                        let uu____76930 =
                          let uu____76937 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____76937
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____76930]  in
                      FStar_Syntax_Subst.open_term uu____76929 body  in
                    match uu____76924 with
                    | (bs,body1) ->
                        (FStar_TypeChecker_Cfg.log cfg
                           (fun uu____76964  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____76973 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____76973  in
                            FStar_Util.Inl
                              (let uu___2199_76989 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2199_76989.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2199_76989.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____76992  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___2204_76995 = lb  in
                             let uu____76996 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___2204_76995.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2204_76995.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____76996;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2204_76995.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2204_76995.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____77025  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___2211_77050 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps =
                                 (uu___2211_77050.FStar_TypeChecker_Cfg.steps);
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___2211_77050.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___2211_77050.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 (uu___2211_77050.FStar_TypeChecker_Cfg.delta_level);
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___2211_77050.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong = true;
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___2211_77050.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___2211_77050.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___2211_77050.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           FStar_TypeChecker_Cfg.log cfg1
                             (fun uu____77054  ->
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
               let uu____77075 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____77075 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____77111 =
                               let uu___2227_77112 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2227_77112.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2227_77112.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____77111  in
                           let uu____77113 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____77113 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____77139 =
                                   FStar_List.map (fun uu____77155  -> dummy)
                                     lbs1
                                    in
                                 let uu____77156 =
                                   let uu____77165 =
                                     FStar_List.map
                                       (fun uu____77187  -> dummy) xs1
                                      in
                                   FStar_List.append uu____77165 env  in
                                 FStar_List.append uu____77139 uu____77156
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____77213 =
                                       let uu___2241_77214 = rc  in
                                       let uu____77215 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___2241_77214.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____77215;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___2241_77214.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____77213
                                 | uu____77224 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___2246_77230 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___2246_77230.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___2246_77230.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___2246_77230.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___2246_77230.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____77240 =
                        FStar_List.map (fun uu____77256  -> dummy) lbs2  in
                      FStar_List.append uu____77240 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____77264 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____77264 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___2255_77280 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___2255_77280.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___2255_77280.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
               ->
               let uu____77314 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____77314
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____77335 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____77413  ->
                        match uu____77413 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___2271_77538 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2271_77538.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___2271_77538.FStar_Syntax_Syntax.sort)
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
               (match uu____77335 with
                | (rec_env,memos,uu____77773) ->
                    let uu____77828 =
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
                             let uu____78140 =
                               let uu____78147 =
                                 let uu____78148 =
                                   let uu____78180 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____78180, false)
                                    in
                                 Clos uu____78148  in
                               (FStar_Pervasives_Native.None, uu____78147)
                                in
                             uu____78140 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____78287  ->
                     let uu____78288 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____78288);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____78312 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____78316::uu____78317 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____78322) ->
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
                             | uu____78353 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____78369 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____78369
                              | uu____78382 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____78388 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____78412 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____78426 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____78440 =
                        let uu____78442 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____78444 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____78442 uu____78444
                         in
                      failwith uu____78440
                    else
                      (let uu____78449 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____78449)
                | uu____78450 -> norm cfg env stack t2))

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
              let uu____78459 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____78459 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____78473  ->
                        let uu____78474 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____78474);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____78487  ->
                        let uu____78488 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____78490 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____78488 uu____78490);
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
                      | (UnivArgs (us',uu____78509))::stack1 ->
                          ((let uu____78518 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____78518
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____78526 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____78526) us'
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
                      | uu____78562 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____78565 ->
                          let uu____78568 =
                            let uu____78570 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____78570
                             in
                          failwith uu____78568
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
                  let uu___2377_78598 = cfg  in
                  let uu____78599 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____78599;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___2377_78598.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___2377_78598.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___2377_78598.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___2377_78598.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___2377_78598.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___2377_78598.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___2377_78598.FStar_TypeChecker_Cfg.reifying)
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
                     (uu____78630,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____78631;
                                    FStar_Syntax_Syntax.vars = uu____78632;_},uu____78633,uu____78634))::uu____78635
                     -> ()
                 | uu____78640 ->
                     let uu____78643 =
                       let uu____78645 = stack_to_string stack  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____78645
                        in
                     failwith uu____78643);
                (let head0 = head1  in
                 let head2 = FStar_Syntax_Util.unascribe head1  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____78654  ->
                      let uu____78655 = FStar_Syntax_Print.tag_of_term head2
                         in
                      let uu____78657 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____78655
                        uu____78657);
                 (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                  let uu____78661 =
                    let uu____78662 = FStar_Syntax_Subst.compress head3  in
                    uu____78662.FStar_Syntax_Syntax.n  in
                  match uu____78661 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let ed =
                        let uu____78683 =
                          FStar_TypeChecker_Env.norm_eff_name
                            cfg.FStar_TypeChecker_Cfg.tcenv m
                           in
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv uu____78683
                         in
                      let uu____78684 = ed.FStar_Syntax_Syntax.bind_repr  in
                      (match uu____78684 with
                       | (uu____78685,bind_repr) ->
                           (match lb.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____78695 ->
                                failwith
                                  "Cannot reify a top-level let binding"
                            | FStar_Util.Inl x ->
                                let is_return e =
                                  let uu____78706 =
                                    let uu____78707 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____78707.FStar_Syntax_Syntax.n  in
                                  match uu____78706 with
                                  | FStar_Syntax_Syntax.Tm_meta
                                      (e1,FStar_Syntax_Syntax.Meta_monadic
                                       (uu____78713,uu____78714))
                                      ->
                                      let uu____78723 =
                                        let uu____78724 =
                                          FStar_Syntax_Subst.compress e1  in
                                        uu____78724.FStar_Syntax_Syntax.n  in
                                      (match uu____78723 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                            (uu____78730,msrc,uu____78732))
                                           when
                                           FStar_Syntax_Util.is_pure_effect
                                             msrc
                                           ->
                                           let uu____78741 =
                                             FStar_Syntax_Subst.compress e2
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____78741
                                       | uu____78742 ->
                                           FStar_Pervasives_Native.None)
                                  | uu____78743 ->
                                      FStar_Pervasives_Native.None
                                   in
                                let uu____78744 =
                                  is_return lb.FStar_Syntax_Syntax.lbdef  in
                                (match uu____78744 with
                                 | FStar_Pervasives_Native.Some e ->
                                     let lb1 =
                                       let uu___2449_78749 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___2449_78749.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___2449_78749.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           (uu___2449_78749.FStar_Syntax_Syntax.lbtyp);
                                         FStar_Syntax_Syntax.lbeff =
                                           FStar_Parser_Const.effect_PURE_lid;
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___2449_78749.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___2449_78749.FStar_Syntax_Syntax.lbpos)
                                       }  in
                                     let uu____78750 = FStar_List.tl stack
                                        in
                                     let uu____78751 =
                                       let uu____78752 =
                                         let uu____78759 =
                                           let uu____78760 =
                                             let uu____78774 =
                                               FStar_Syntax_Util.mk_reify
                                                 body
                                                in
                                             ((false, [lb1]), uu____78774)
                                              in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____78760
                                            in
                                         FStar_Syntax_Syntax.mk uu____78759
                                          in
                                       uu____78752
                                         FStar_Pervasives_Native.None
                                         head3.FStar_Syntax_Syntax.pos
                                        in
                                     norm cfg env uu____78750 uu____78751
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____78793 =
                                       let uu____78795 = is_return body  in
                                       match uu____78795 with
                                       | FStar_Pervasives_Native.Some
                                           {
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_bvar y;
                                             FStar_Syntax_Syntax.pos =
                                               uu____78800;
                                             FStar_Syntax_Syntax.vars =
                                               uu____78801;_}
                                           -> FStar_Syntax_Syntax.bv_eq x y
                                       | uu____78804 -> false  in
                                     if uu____78793
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
                                          let uu____78828 =
                                            let uu____78835 =
                                              let uu____78836 =
                                                let uu____78855 =
                                                  let uu____78864 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____78864]  in
                                                (uu____78855, body1,
                                                  (FStar_Pervasives_Native.Some
                                                     body_rc))
                                                 in
                                              FStar_Syntax_Syntax.Tm_abs
                                                uu____78836
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____78835
                                             in
                                          uu____78828
                                            FStar_Pervasives_Native.None
                                            body1.FStar_Syntax_Syntax.pos
                                           in
                                        let close1 = closure_as_term cfg env
                                           in
                                        let bind_inst =
                                          let uu____78906 =
                                            let uu____78907 =
                                              FStar_Syntax_Subst.compress
                                                bind_repr
                                               in
                                            uu____78907.FStar_Syntax_Syntax.n
                                             in
                                          match uu____78906 with
                                          | FStar_Syntax_Syntax.Tm_uinst
                                              (bind1,uu____78913::uu____78914::[])
                                              ->
                                              let uu____78919 =
                                                let uu____78926 =
                                                  let uu____78927 =
                                                    let uu____78934 =
                                                      let uu____78935 =
                                                        let uu____78936 =
                                                          close1
                                                            lb.FStar_Syntax_Syntax.lbtyp
                                                           in
                                                        (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.FStar_TypeChecker_Cfg.tcenv
                                                          uu____78936
                                                         in
                                                      let uu____78937 =
                                                        let uu____78940 =
                                                          let uu____78941 =
                                                            close1 t  in
                                                          (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                            cfg.FStar_TypeChecker_Cfg.tcenv
                                                            uu____78941
                                                           in
                                                        [uu____78940]  in
                                                      uu____78935 ::
                                                        uu____78937
                                                       in
                                                    (bind1, uu____78934)  in
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                    uu____78927
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____78926
                                                 in
                                              uu____78919
                                                FStar_Pervasives_Native.None
                                                rng
                                          | uu____78947 ->
                                              failwith
                                                "NIY : Reification of indexed effects"
                                           in
                                        let maybe_range_arg =
                                          let uu____78962 =
                                            FStar_Util.for_some
                                              (FStar_Syntax_Util.attr_eq
                                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                                              ed.FStar_Syntax_Syntax.eff_attrs
                                             in
                                          if uu____78962
                                          then
                                            let uu____78975 =
                                              let uu____78984 =
                                                FStar_TypeChecker_Cfg.embed_simple
                                                  FStar_Syntax_Embeddings.e_range
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____78984
                                               in
                                            let uu____78985 =
                                              let uu____78996 =
                                                let uu____79005 =
                                                  FStar_TypeChecker_Cfg.embed_simple
                                                    FStar_Syntax_Embeddings.e_range
                                                    body2.FStar_Syntax_Syntax.pos
                                                    body2.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Syntax_Syntax.as_arg
                                                  uu____79005
                                                 in
                                              [uu____78996]  in
                                            uu____78975 :: uu____78985
                                          else []  in
                                        let reified =
                                          let uu____79043 =
                                            let uu____79050 =
                                              let uu____79051 =
                                                let uu____79068 =
                                                  let uu____79079 =
                                                    let uu____79090 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        lb.FStar_Syntax_Syntax.lbtyp
                                                       in
                                                    let uu____79099 =
                                                      let uu____79110 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          t
                                                         in
                                                      [uu____79110]  in
                                                    uu____79090 ::
                                                      uu____79099
                                                     in
                                                  let uu____79143 =
                                                    let uu____79154 =
                                                      let uu____79165 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          FStar_Syntax_Syntax.tun
                                                         in
                                                      let uu____79174 =
                                                        let uu____79185 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            head4
                                                           in
                                                        let uu____79194 =
                                                          let uu____79205 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          let uu____79214 =
                                                            let uu____79225 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                body2
                                                               in
                                                            [uu____79225]  in
                                                          uu____79205 ::
                                                            uu____79214
                                                           in
                                                        uu____79185 ::
                                                          uu____79194
                                                         in
                                                      uu____79165 ::
                                                        uu____79174
                                                       in
                                                    FStar_List.append
                                                      maybe_range_arg
                                                      uu____79154
                                                     in
                                                  FStar_List.append
                                                    uu____79079 uu____79143
                                                   in
                                                (bind_inst, uu____79068)  in
                                              FStar_Syntax_Syntax.Tm_app
                                                uu____79051
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____79050
                                             in
                                          uu____79043
                                            FStar_Pervasives_Native.None rng
                                           in
                                        FStar_TypeChecker_Cfg.log cfg
                                          (fun uu____79309  ->
                                             let uu____79310 =
                                               FStar_Syntax_Print.term_to_string
                                                 head0
                                                in
                                             let uu____79312 =
                                               FStar_Syntax_Print.term_to_string
                                                 reified
                                                in
                                             FStar_Util.print2
                                               "Reified (1) <%s> to %s\n"
                                               uu____79310 uu____79312);
                                        (let uu____79315 =
                                           FStar_List.tl stack  in
                                         norm cfg env uu____79315 reified)))))
                  | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                      ((let uu____79343 = FStar_Options.defensive ()  in
                        if uu____79343
                        then
                          let is_arg_impure uu____79358 =
                            match uu____79358 with
                            | (e,q) ->
                                let uu____79372 =
                                  let uu____79373 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____79373.FStar_Syntax_Syntax.n  in
                                (match uu____79372 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____79389 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____79389
                                 | uu____79391 -> false)
                             in
                          let uu____79393 =
                            let uu____79395 =
                              let uu____79406 =
                                FStar_Syntax_Syntax.as_arg head_app  in
                              uu____79406 :: args  in
                            FStar_Util.for_some is_arg_impure uu____79395  in
                          (if uu____79393
                           then
                             let uu____79432 =
                               let uu____79438 =
                                 let uu____79440 =
                                   FStar_Syntax_Print.term_to_string head3
                                    in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____79440
                                  in
                               (FStar_Errors.Warning_Defensive, uu____79438)
                                in
                             FStar_Errors.log_issue
                               head3.FStar_Syntax_Syntax.pos uu____79432
                           else ())
                        else ());
                       (let fallback1 uu____79453 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____79457  ->
                               let uu____79458 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____79458 "");
                          (let uu____79462 = FStar_List.tl stack  in
                           let uu____79463 = FStar_Syntax_Util.mk_reify head3
                              in
                           norm cfg env uu____79462 uu____79463)
                           in
                        let fallback2 uu____79469 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____79473  ->
                               let uu____79474 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____79474 "");
                          (let uu____79478 = FStar_List.tl stack  in
                           let uu____79479 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (head3,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               head0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env uu____79478 uu____79479)
                           in
                        let uu____79484 =
                          let uu____79485 =
                            FStar_Syntax_Util.un_uinst head_app  in
                          uu____79485.FStar_Syntax_Syntax.n  in
                        match uu____79484 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____79491 =
                              let uu____79493 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____79493  in
                            if uu____79491
                            then fallback1 ()
                            else
                              (let uu____79498 =
                                 let uu____79500 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____79500  in
                               if uu____79498
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____79517 =
                                      let uu____79522 =
                                        FStar_Syntax_Util.mk_reify head_app
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____79522 args
                                       in
                                    uu____79517 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____79525 = FStar_List.tl stack  in
                                  norm cfg env uu____79525 t1))
                        | uu____79526 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____79528) ->
                      do_reify_monadic fallback cfg env stack e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____79552 = closure_as_term cfg env t'  in
                        reify_lift cfg e msrc mtgt uu____79552  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____79556  ->
                            let uu____79557 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____79557);
                       (let uu____79560 = FStar_List.tl stack  in
                        norm cfg env uu____79560 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                      let branches1 =
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun uu____79681  ->
                                match uu____79681 with
                                | (pat,wopt,tm) ->
                                    let uu____79729 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____79729)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                          head3.FStar_Syntax_Syntax.pos
                         in
                      let uu____79761 = FStar_List.tl stack  in
                      norm cfg env uu____79761 tm
                  | uu____79762 -> fallback ()))

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
              (fun uu____79776  ->
                 let uu____79777 = FStar_Ident.string_of_lid msrc  in
                 let uu____79779 = FStar_Ident.string_of_lid mtgt  in
                 let uu____79781 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____79777
                   uu____79779 uu____79781);
            (let uu____79784 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____79784
             then
               let ed =
                 let uu____79788 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____79788  in
               let uu____79789 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____79789 with
               | (uu____79790,return_repr) ->
                   let return_inst =
                     let uu____79803 =
                       let uu____79804 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____79804.FStar_Syntax_Syntax.n  in
                     match uu____79803 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____79810::[]) ->
                         let uu____79815 =
                           let uu____79822 =
                             let uu____79823 =
                               let uu____79830 =
                                 let uu____79831 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____79831]  in
                               (return_tm, uu____79830)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____79823  in
                           FStar_Syntax_Syntax.mk uu____79822  in
                         uu____79815 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____79837 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____79841 =
                     let uu____79848 =
                       let uu____79849 =
                         let uu____79866 =
                           let uu____79877 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____79886 =
                             let uu____79897 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____79897]  in
                           uu____79877 :: uu____79886  in
                         (return_inst, uu____79866)  in
                       FStar_Syntax_Syntax.Tm_app uu____79849  in
                     FStar_Syntax_Syntax.mk uu____79848  in
                   uu____79841 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____79947 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____79947 with
                | FStar_Pervasives_Native.None  ->
                    let uu____79950 =
                      let uu____79952 = FStar_Ident.text_of_lid msrc  in
                      let uu____79954 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____79952 uu____79954
                       in
                    failwith uu____79950
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____79957;
                      FStar_TypeChecker_Env.mtarget = uu____79958;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____79959;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____79981 =
                      let uu____79983 = FStar_Ident.text_of_lid msrc  in
                      let uu____79985 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____79983 uu____79985
                       in
                    failwith uu____79981
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____79988;
                      FStar_TypeChecker_Env.mtarget = uu____79989;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____79990;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____80025 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____80026 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____80025 t FStar_Syntax_Syntax.tun uu____80026))

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
                (fun uu____80096  ->
                   match uu____80096 with
                   | (a,imp) ->
                       let uu____80115 = norm cfg env [] a  in
                       (uu____80115, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____80125  ->
             let uu____80126 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____80128 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____80126 uu____80128);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____80154 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _80157  -> FStar_Pervasives_Native.Some _80157)
                     uu____80154
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2599_80158 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2599_80158.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2599_80158.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____80180 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _80183  -> FStar_Pervasives_Native.Some _80183)
                     uu____80180
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2610_80184 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2610_80184.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2610_80184.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____80229  ->
                      match uu____80229 with
                      | (a,i) ->
                          let uu____80249 = norm cfg env [] a  in
                          (uu____80249, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___600_80271  ->
                       match uu___600_80271 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____80275 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____80275
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___2627_80283 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2629_80286 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2629_80286.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2627_80283.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2627_80283.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun b  ->
        let uu____80290 = b  in
        match uu____80290 with
        | (x,imp) ->
            let x1 =
              let uu___2637_80298 = x  in
              let uu____80299 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2637_80298.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2637_80298.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____80299
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____80310 =
                    let uu____80311 = closure_as_term cfg env t  in
                    FStar_Syntax_Syntax.Meta uu____80311  in
                  FStar_Pervasives_Native.Some uu____80310
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____80322 =
          FStar_List.fold_left
            (fun uu____80356  ->
               fun b  ->
                 match uu____80356 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____80322 with | (nbs,uu____80436) -> FStar_List.rev nbs

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
            let uu____80468 =
              let uu___2662_80469 = rc  in
              let uu____80470 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2662_80469.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____80470;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2662_80469.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____80468
        | uu____80479 -> lopt

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
            (let uu____80489 = FStar_Syntax_Print.term_to_string tm  in
             let uu____80491 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____80489 uu____80491)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___601_80503  ->
      match uu___601_80503 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____80516 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____80516 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____80520 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____80520)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____80528 = norm_cb cfg  in
            reduce_primops uu____80528 cfg env tm  in
          let uu____80535 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____80535
          then tm1
          else
            (let w t =
               let uu___2690_80554 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2690_80554.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2690_80554.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____80566 =
                 let uu____80567 = FStar_Syntax_Util.unmeta t  in
                 uu____80567.FStar_Syntax_Syntax.n  in
               match uu____80566 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____80579 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____80643)::args1,(bv,uu____80646)::bs1) ->
                   let uu____80700 =
                     let uu____80701 = FStar_Syntax_Subst.compress t  in
                     uu____80701.FStar_Syntax_Syntax.n  in
                   (match uu____80700 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____80706 -> false)
               | ([],[]) -> true
               | (uu____80737,uu____80738) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____80789 = FStar_Syntax_Print.term_to_string t  in
                  let uu____80791 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____80789
                    uu____80791)
               else ();
               (let uu____80796 = FStar_Syntax_Util.head_and_args' t  in
                match uu____80796 with
                | (hd1,args) ->
                    let uu____80835 =
                      let uu____80836 = FStar_Syntax_Subst.compress hd1  in
                      uu____80836.FStar_Syntax_Syntax.n  in
                    (match uu____80835 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____80844 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____80846 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____80848 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____80844 uu____80846 uu____80848)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____80853 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____80871 = FStar_Syntax_Print.term_to_string t  in
                  let uu____80873 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____80871
                    uu____80873)
               else ();
               (let uu____80878 = FStar_Syntax_Util.is_squash t  in
                match uu____80878 with
                | FStar_Pervasives_Native.Some (uu____80889,t') ->
                    is_applied bs t'
                | uu____80901 ->
                    let uu____80910 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____80910 with
                     | FStar_Pervasives_Native.Some (uu____80921,t') ->
                         is_applied bs t'
                     | uu____80933 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____80957 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____80957 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____80964)::(q,uu____80966)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____81009 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____81011 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____81009 uu____81011)
                    else ();
                    (let uu____81016 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____81016 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____81021 =
                           let uu____81022 = FStar_Syntax_Subst.compress p
                              in
                           uu____81022.FStar_Syntax_Syntax.n  in
                         (match uu____81021 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____81033 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____81033))
                          | uu____81036 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____81039)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____81064 =
                           let uu____81065 = FStar_Syntax_Subst.compress p1
                              in
                           uu____81065.FStar_Syntax_Syntax.n  in
                         (match uu____81064 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____81076 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____81076))
                          | uu____81079 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____81083 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____81083 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____81088 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____81088 with
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
                                     let uu____81102 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____81102))
                               | uu____81105 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____81110)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____81135 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____81135 with
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
                                     let uu____81149 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____81149))
                               | uu____81152 -> FStar_Pervasives_Native.None)
                          | uu____81155 -> FStar_Pervasives_Native.None)
                     | uu____81158 -> FStar_Pervasives_Native.None))
               | uu____81161 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____81174 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____81174 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____81180)::[],uu____81181,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____81201 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____81203 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____81201
                         uu____81203)
                    else ();
                    is_quantified_const bv phi')
               | uu____81208 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____81223 =
                 let uu____81224 = FStar_Syntax_Subst.compress phi  in
                 uu____81224.FStar_Syntax_Syntax.n  in
               match uu____81223 with
               | FStar_Syntax_Syntax.Tm_match (uu____81230,br::brs) ->
                   let uu____81297 = br  in
                   (match uu____81297 with
                    | (uu____81315,uu____81316,e) ->
                        let r =
                          let uu____81338 = simp_t e  in
                          match uu____81338 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____81350 =
                                FStar_List.for_all
                                  (fun uu____81369  ->
                                     match uu____81369 with
                                     | (uu____81383,uu____81384,e') ->
                                         let uu____81398 = simp_t e'  in
                                         uu____81398 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____81350
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____81414 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____81424 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____81424
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____81462 =
                 match uu____81462 with
                 | (t1,q) ->
                     let uu____81483 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____81483 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____81515 -> (t1, q))
                  in
               let uu____81528 = FStar_Syntax_Util.head_and_args t  in
               match uu____81528 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____81608 =
                 let uu____81609 = FStar_Syntax_Util.unmeta ty  in
                 uu____81609.FStar_Syntax_Syntax.n  in
               match uu____81608 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____81614) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____81619,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____81643 -> false  in
             let simplify1 arg =
               let uu____81676 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____81676, arg)  in
             let uu____81691 = is_forall_const tm1  in
             match uu____81691 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____81697 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____81699 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____81697
                       uu____81699)
                  else ();
                  (let uu____81704 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____81704))
             | FStar_Pervasives_Native.None  ->
                 let uu____81705 =
                   let uu____81706 = FStar_Syntax_Subst.compress tm1  in
                   uu____81706.FStar_Syntax_Syntax.n  in
                 (match uu____81705 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____81710;
                              FStar_Syntax_Syntax.vars = uu____81711;_},uu____81712);
                         FStar_Syntax_Syntax.pos = uu____81713;
                         FStar_Syntax_Syntax.vars = uu____81714;_},args)
                      ->
                      let uu____81744 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____81744
                      then
                        let uu____81747 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____81747 with
                         | (FStar_Pervasives_Native.Some (true ),uu____81805)::
                             (uu____81806,(arg,uu____81808))::[] ->
                             maybe_auto_squash arg
                         | (uu____81881,(arg,uu____81883))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____81884)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____81957)::uu____81958::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____82028::(FStar_Pervasives_Native.Some (false
                                         ),uu____82029)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____82099 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____82117 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____82117
                         then
                           let uu____82120 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____82120 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____82178)::uu____82179::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____82249::(FStar_Pervasives_Native.Some (true
                                           ),uu____82250)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____82320)::(uu____82321,(arg,uu____82323))::[]
                               -> maybe_auto_squash arg
                           | (uu____82396,(arg,uu____82398))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____82399)::[]
                               -> maybe_auto_squash arg
                           | uu____82472 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____82490 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____82490
                            then
                              let uu____82493 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____82493 with
                              | uu____82551::(FStar_Pervasives_Native.Some
                                              (true ),uu____82552)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____82622)::uu____82623::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____82693)::(uu____82694,(arg,uu____82696))::[]
                                  -> maybe_auto_squash arg
                              | (uu____82769,(p,uu____82771))::(uu____82772,
                                                                (q,uu____82774))::[]
                                  ->
                                  let uu____82846 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____82846
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____82851 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____82869 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____82869
                               then
                                 let uu____82872 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____82872 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____82930)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____82931)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____83005)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____83006)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____83080)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____83081)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____83155)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____83156)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____83230,(arg,uu____83232))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____83233)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____83306)::(uu____83307,(arg,uu____83309))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____83382,(arg,uu____83384))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____83385)::[]
                                     ->
                                     let uu____83458 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____83458
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____83459)::(uu____83460,(arg,uu____83462))::[]
                                     ->
                                     let uu____83535 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____83535
                                 | (uu____83536,(p,uu____83538))::(uu____83539,
                                                                   (q,uu____83541))::[]
                                     ->
                                     let uu____83613 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____83613
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____83618 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____83636 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____83636
                                  then
                                    let uu____83639 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____83639 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____83697)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____83741)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____83785 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____83803 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____83803
                                     then
                                       match args with
                                       | (t,uu____83807)::[] ->
                                           let uu____83832 =
                                             let uu____83833 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____83833.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____83832 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____83836::[],body,uu____83838)
                                                ->
                                                let uu____83873 = simp_t body
                                                   in
                                                (match uu____83873 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____83879 -> tm1)
                                            | uu____83883 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____83885))::(t,uu____83887)::[]
                                           ->
                                           let uu____83927 =
                                             let uu____83928 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____83928.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____83927 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____83931::[],body,uu____83933)
                                                ->
                                                let uu____83968 = simp_t body
                                                   in
                                                (match uu____83968 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____83976 -> tm1)
                                            | uu____83980 -> tm1)
                                       | uu____83981 -> tm1
                                     else
                                       (let uu____83994 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____83994
                                        then
                                          match args with
                                          | (t,uu____83998)::[] ->
                                              let uu____84023 =
                                                let uu____84024 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____84024.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____84023 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____84027::[],body,uu____84029)
                                                   ->
                                                   let uu____84064 =
                                                     simp_t body  in
                                                   (match uu____84064 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____84070 -> tm1)
                                               | uu____84074 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____84076))::(t,uu____84078)::[]
                                              ->
                                              let uu____84118 =
                                                let uu____84119 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____84119.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____84118 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____84122::[],body,uu____84124)
                                                   ->
                                                   let uu____84159 =
                                                     simp_t body  in
                                                   (match uu____84159 with
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
                                                    | uu____84167 -> tm1)
                                               | uu____84171 -> tm1)
                                          | uu____84172 -> tm1
                                        else
                                          (let uu____84185 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____84185
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____84188;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____84189;_},uu____84190)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____84216;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____84217;_},uu____84218)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____84244 -> tm1
                                           else
                                             (let uu____84257 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____84257
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____84271 =
                                                    let uu____84272 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____84272.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____84271 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____84283 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     (Prims.parse_int "1")
                                                 then
                                                   let t =
                                                     let uu____84297 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____84297
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____84336 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____84336
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____84342 =
                                                         let uu____84343 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____84343.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____84342 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____84346 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____84354 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____84354
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____84363
                                                                  =
                                                                  let uu____84364
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____84364.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____84363
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____84370)
                                                                    -> hd1
                                                                | uu____84395
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____84399
                                                                =
                                                                let uu____84410
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____84410]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____84399)
                                                       | uu____84443 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____84448 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____84448 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____84468 ->
                                                     let uu____84477 =
                                                       let uu____84484 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____84484 cfg env
                                                        in
                                                     uu____84477 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____84492;
                         FStar_Syntax_Syntax.vars = uu____84493;_},args)
                      ->
                      let uu____84519 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____84519
                      then
                        let uu____84522 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____84522 with
                         | (FStar_Pervasives_Native.Some (true ),uu____84580)::
                             (uu____84581,(arg,uu____84583))::[] ->
                             maybe_auto_squash arg
                         | (uu____84656,(arg,uu____84658))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____84659)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____84732)::uu____84733::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____84803::(FStar_Pervasives_Native.Some (false
                                         ),uu____84804)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____84874 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____84892 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____84892
                         then
                           let uu____84895 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____84895 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____84953)::uu____84954::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____85024::(FStar_Pervasives_Native.Some (true
                                           ),uu____85025)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____85095)::(uu____85096,(arg,uu____85098))::[]
                               -> maybe_auto_squash arg
                           | (uu____85171,(arg,uu____85173))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____85174)::[]
                               -> maybe_auto_squash arg
                           | uu____85247 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____85265 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____85265
                            then
                              let uu____85268 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____85268 with
                              | uu____85326::(FStar_Pervasives_Native.Some
                                              (true ),uu____85327)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____85397)::uu____85398::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____85468)::(uu____85469,(arg,uu____85471))::[]
                                  -> maybe_auto_squash arg
                              | (uu____85544,(p,uu____85546))::(uu____85547,
                                                                (q,uu____85549))::[]
                                  ->
                                  let uu____85621 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____85621
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____85626 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____85644 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____85644
                               then
                                 let uu____85647 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____85647 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____85705)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____85706)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____85780)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____85781)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____85855)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____85856)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____85930)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____85931)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____86005,(arg,uu____86007))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____86008)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____86081)::(uu____86082,(arg,uu____86084))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____86157,(arg,uu____86159))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____86160)::[]
                                     ->
                                     let uu____86233 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____86233
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____86234)::(uu____86235,(arg,uu____86237))::[]
                                     ->
                                     let uu____86310 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____86310
                                 | (uu____86311,(p,uu____86313))::(uu____86314,
                                                                   (q,uu____86316))::[]
                                     ->
                                     let uu____86388 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____86388
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____86393 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____86411 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____86411
                                  then
                                    let uu____86414 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____86414 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____86472)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____86516)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____86560 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____86578 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____86578
                                     then
                                       match args with
                                       | (t,uu____86582)::[] ->
                                           let uu____86607 =
                                             let uu____86608 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____86608.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____86607 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____86611::[],body,uu____86613)
                                                ->
                                                let uu____86648 = simp_t body
                                                   in
                                                (match uu____86648 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____86654 -> tm1)
                                            | uu____86658 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____86660))::(t,uu____86662)::[]
                                           ->
                                           let uu____86702 =
                                             let uu____86703 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____86703.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____86702 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____86706::[],body,uu____86708)
                                                ->
                                                let uu____86743 = simp_t body
                                                   in
                                                (match uu____86743 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____86751 -> tm1)
                                            | uu____86755 -> tm1)
                                       | uu____86756 -> tm1
                                     else
                                       (let uu____86769 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____86769
                                        then
                                          match args with
                                          | (t,uu____86773)::[] ->
                                              let uu____86798 =
                                                let uu____86799 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____86799.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____86798 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____86802::[],body,uu____86804)
                                                   ->
                                                   let uu____86839 =
                                                     simp_t body  in
                                                   (match uu____86839 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____86845 -> tm1)
                                               | uu____86849 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____86851))::(t,uu____86853)::[]
                                              ->
                                              let uu____86893 =
                                                let uu____86894 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____86894.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____86893 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____86897::[],body,uu____86899)
                                                   ->
                                                   let uu____86934 =
                                                     simp_t body  in
                                                   (match uu____86934 with
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
                                                    | uu____86942 -> tm1)
                                               | uu____86946 -> tm1)
                                          | uu____86947 -> tm1
                                        else
                                          (let uu____86960 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____86960
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____86963;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____86964;_},uu____86965)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____86991;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____86992;_},uu____86993)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____87019 -> tm1
                                           else
                                             (let uu____87032 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____87032
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____87046 =
                                                    let uu____87047 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____87047.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____87046 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____87058 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     (Prims.parse_int "1")
                                                 then
                                                   let t =
                                                     let uu____87072 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____87072
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____87107 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____87107
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____87113 =
                                                         let uu____87114 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____87114.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____87113 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____87117 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____87125 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____87125
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____87134
                                                                  =
                                                                  let uu____87135
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____87135.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____87134
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____87141)
                                                                    -> hd1
                                                                | uu____87166
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____87170
                                                                =
                                                                let uu____87181
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____87181]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____87170)
                                                       | uu____87214 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____87219 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____87219 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____87239 ->
                                                     let uu____87248 =
                                                       let uu____87255 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____87255 cfg env
                                                        in
                                                     uu____87248 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____87268 = simp_t t  in
                      (match uu____87268 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____87277 ->
                      let uu____87300 = is_const_match tm1  in
                      (match uu____87300 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____87309 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____87319  ->
               (let uu____87321 = FStar_Syntax_Print.tag_of_term t  in
                let uu____87323 = FStar_Syntax_Print.term_to_string t  in
                let uu____87325 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____87333 =
                  let uu____87335 =
                    let uu____87338 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____87338
                     in
                  stack_to_string uu____87335  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____87321 uu____87323 uu____87325 uu____87333);
               (let uu____87363 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____87363
                then
                  let uu____87367 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____87367 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____87374 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____87376 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____87378 =
                          let uu____87380 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____87380
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____87374
                          uu____87376 uu____87378);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____87402 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack with
                | (Arg uu____87410)::uu____87411 -> true
                | uu____87421 -> false)
              in
           if uu____87402
           then
             let uu____87424 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____87424 (norm cfg env stack)
           else
             (let t1 = maybe_simplify cfg env stack t  in
              match stack with
              | [] -> t1
              | (Debug (tm,time_then))::stack1 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now ()  in
                      let uu____87438 =
                        let uu____87440 =
                          let uu____87442 =
                            FStar_Util.time_diff time_then time_now  in
                          FStar_Pervasives_Native.snd uu____87442  in
                        FStar_Util.string_of_int uu____87440  in
                      let uu____87449 = FStar_Syntax_Print.term_to_string tm
                         in
                      let uu____87451 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print3
                        "Normalized term (%s ms) %s\n\tto term %s\n"
                        uu____87438 uu____87449 uu____87451)
                   else ();
                   rebuild cfg env stack1 t1)
              | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
              | (Meta (uu____87460,m,r))::stack1 ->
                  let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
                  rebuild cfg env stack1 t2
              | (MemoLazy r)::stack1 ->
                  (set_memo cfg r (env, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu____87511  ->
                        let uu____87512 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 "\tSet memo %s\n" uu____87512);
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
                  let uu____87555 =
                    let uu___3319_87556 = FStar_Syntax_Util.abs bs1 t1 lopt1
                       in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___3319_87556.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___3319_87556.FStar_Syntax_Syntax.vars)
                    }  in
                  rebuild cfg env stack1 uu____87555
              | (Arg (Univ uu____87559,uu____87560,uu____87561))::uu____87562
                  -> failwith "Impossible"
              | (Arg (Dummy ,uu____87566,uu____87567))::uu____87568 ->
                  failwith "Impossible"
              | (UnivArgs (us,r))::stack1 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                  rebuild cfg env stack1 t2
              | (Arg
                  (Clos (env_arg,tm,uu____87584,uu____87585),aq,r))::stack1
                  when
                  let uu____87637 = head_of t1  in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____87637 ->
                  let t2 =
                    let uu____87641 =
                      let uu____87646 =
                        let uu____87647 = closure_as_term cfg env_arg tm  in
                        (uu____87647, aq)  in
                      FStar_Syntax_Syntax.extend_app t1 uu____87646  in
                    uu____87641 FStar_Pervasives_Native.None r  in
                  rebuild cfg env stack1 t2
              | (Arg (Clos (env_arg,tm,m,uu____87659),aq,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____87714  ->
                        let uu____87715 =
                          FStar_Syntax_Print.term_to_string tm  in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____87715);
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
                     (let uu____87735 = FStar_ST.op_Bang m  in
                      match uu____87735 with
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
                      | FStar_Pervasives_Native.Some (uu____87878,a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq)
                              FStar_Pervasives_Native.None r
                             in
                          rebuild cfg env_arg stack1 t2))
              | (App (env1,head1,aq,r))::stack' when should_reify cfg stack
                  ->
                  let t0 = t1  in
                  let fallback msg uu____87934 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____87939  ->
                         let uu____87940 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____87940);
                    (let t2 =
                       FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env1 stack' t2)
                     in
                  let uu____87950 =
                    let uu____87951 = FStar_Syntax_Subst.compress t1  in
                    uu____87951.FStar_Syntax_Syntax.n  in
                  (match uu____87950 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env1 stack t2 m
                         ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc,mtgt,ty))
                       ->
                       let lifted =
                         let uu____87979 = closure_as_term cfg env1 ty  in
                         reify_lift cfg t2 msrc mtgt uu____87979  in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____87983  ->
                             let uu____87984 =
                               FStar_Syntax_Print.term_to_string lifted  in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____87984);
                        (let uu____87987 = FStar_List.tl stack  in
                         norm cfg env1 uu____87987 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu____87988);
                          FStar_Syntax_Syntax.pos = uu____87989;
                          FStar_Syntax_Syntax.vars = uu____87990;_},(e,uu____87992)::[])
                       -> norm cfg env1 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____88031 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____88048 = FStar_Syntax_Util.head_and_args t1
                          in
                       (match uu____88048 with
                        | (hd1,args) ->
                            let uu____88091 =
                              let uu____88092 =
                                FStar_Syntax_Util.un_uinst hd1  in
                              uu____88092.FStar_Syntax_Syntax.n  in
                            (match uu____88091 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____88096 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv
                                    in
                                 (match uu____88096 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____88099;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____88100;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____88101;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n1;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____88103;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____88104;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____88105;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____88106;_}
                                      when (FStar_List.length args) = n1 ->
                                      norm cfg env1 stack' t1
                                  | uu____88143 -> fallback " (3)" ())
                             | uu____88147 -> fallback " (4)" ()))
                   | uu____88149 -> fallback " (2)" ())
              | (App (env1,head1,aq,r))::stack1 ->
                  let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack1 t2
              | (Match (env',branches,cfg1,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____88175  ->
                        let uu____88176 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____88176);
                   (let scrutinee_env = env  in
                    let env1 = env'  in
                    let scrutinee = t1  in
                    let norm_and_rebuild_match uu____88187 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____88192  ->
                           let uu____88193 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           let uu____88195 =
                             let uu____88197 =
                               FStar_All.pipe_right branches
                                 (FStar_List.map
                                    (fun uu____88227  ->
                                       match uu____88227 with
                                       | (p,uu____88238,uu____88239) ->
                                           FStar_Syntax_Print.pat_to_string p))
                                in
                             FStar_All.pipe_right uu____88197
                               (FStar_String.concat "\n\t")
                              in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu____88193 uu____88195);
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
                                (fun uu___602_88261  ->
                                   match uu___602_88261 with
                                   | FStar_TypeChecker_Env.InliningDelta  ->
                                       true
                                   | FStar_TypeChecker_Env.Eager_unfolding_only
                                        -> true
                                   | uu____88265 -> false))
                            in
                         let steps =
                           let uu___3487_88268 =
                             cfg1.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___3487_88268.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___3487_88268.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta = false;
                             FStar_TypeChecker_Cfg.weak =
                               (uu___3487_88268.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___3487_88268.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___3487_88268.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___3487_88268.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_only =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___3487_88268.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_tac = false;
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___3487_88268.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___3487_88268.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___3487_88268.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___3487_88268.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___3487_88268.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___3487_88268.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___3487_88268.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___3487_88268.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___3487_88268.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___3487_88268.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___3487_88268.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___3487_88268.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___3487_88268.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___3487_88268.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         let uu___3490_88275 = cfg1  in
                         {
                           FStar_TypeChecker_Cfg.steps = steps;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___3490_88275.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___3490_88275.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = new_delta;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___3490_88275.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong = true;
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___3490_88275.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets =
                             (uu___3490_88275.FStar_TypeChecker_Cfg.normalize_pure_lets);
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___3490_88275.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let norm_or_whnf env2 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env2 t2
                         else norm cfg_exclude_zeta env2 [] t2  in
                       let rec norm_pat env2 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu____88350 ->
                             (p, env2)
                         | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                             let uu____88381 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____88470  ->
                                       fun uu____88471  ->
                                         match (uu____88470, uu____88471)
                                         with
                                         | ((pats1,env3),(p1,b)) ->
                                             let uu____88621 =
                                               norm_pat env3 p1  in
                                             (match uu____88621 with
                                              | (p2,env4) ->
                                                  (((p2, b) :: pats1), env4)))
                                    ([], env2))
                                in
                             (match uu____88381 with
                              | (pats1,env3) ->
                                  ((let uu___3518_88791 = p  in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___3518_88791.FStar_Syntax_Syntax.p)
                                    }), env3))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___3522_88812 = x  in
                               let uu____88813 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3522_88812.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3522_88812.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____88813
                               }  in
                             ((let uu___3525_88827 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3525_88827.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___3529_88838 = x  in
                               let uu____88839 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3529_88838.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3529_88838.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____88839
                               }  in
                             ((let uu___3532_88853 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3532_88853.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                             let x1 =
                               let uu___3538_88869 = x  in
                               let uu____88870 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3538_88869.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3538_88869.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____88870
                               }  in
                             let t3 = norm_or_whnf env2 t2  in
                             ((let uu___3542_88885 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___3542_88885.FStar_Syntax_Syntax.p)
                               }), env2)
                          in
                       let branches1 =
                         match env1 with
                         | [] when whnf -> branches
                         | uu____88929 ->
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun branch1  ->
                                     let uu____88959 =
                                       FStar_Syntax_Subst.open_branch branch1
                                        in
                                     match uu____88959 with
                                     | (p,wopt,e) ->
                                         let uu____88979 = norm_pat env1 p
                                            in
                                         (match uu____88979 with
                                          | (p1,env2) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu____89034 =
                                                      norm_or_whnf env2 w  in
                                                    FStar_Pervasives_Native.Some
                                                      uu____89034
                                                 in
                                              let e1 = norm_or_whnf env2 e
                                                 in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1))))
                          in
                       let scrutinee1 =
                         let uu____89051 =
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
                         if uu____89051
                         then
                           norm
                             (let uu___3561_89058 = cfg1  in
                              {
                                FStar_TypeChecker_Cfg.steps =
                                  (let uu___3563_89061 =
                                     cfg1.FStar_TypeChecker_Cfg.steps  in
                                   {
                                     FStar_TypeChecker_Cfg.beta =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.beta);
                                     FStar_TypeChecker_Cfg.iota =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.iota);
                                     FStar_TypeChecker_Cfg.zeta =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.zeta);
                                     FStar_TypeChecker_Cfg.weak =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.weak);
                                     FStar_TypeChecker_Cfg.hnf =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.hnf);
                                     FStar_TypeChecker_Cfg.primops =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.primops);
                                     FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                       =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                     FStar_TypeChecker_Cfg.unfold_until =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.unfold_until);
                                     FStar_TypeChecker_Cfg.unfold_only =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.unfold_only);
                                     FStar_TypeChecker_Cfg.unfold_fully =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.unfold_fully);
                                     FStar_TypeChecker_Cfg.unfold_attr =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.unfold_attr);
                                     FStar_TypeChecker_Cfg.unfold_tac =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.unfold_tac);
                                     FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                       =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                     FStar_TypeChecker_Cfg.simplify =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.simplify);
                                     FStar_TypeChecker_Cfg.erase_universes =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.erase_universes);
                                     FStar_TypeChecker_Cfg.allow_unbound_universes
                                       =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                     FStar_TypeChecker_Cfg.reify_ =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.reify_);
                                     FStar_TypeChecker_Cfg.compress_uvars =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.compress_uvars);
                                     FStar_TypeChecker_Cfg.no_full_norm =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.no_full_norm);
                                     FStar_TypeChecker_Cfg.check_no_uvars =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.check_no_uvars);
                                     FStar_TypeChecker_Cfg.unmeta =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.unmeta);
                                     FStar_TypeChecker_Cfg.unascribe =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.unascribe);
                                     FStar_TypeChecker_Cfg.in_full_norm_request
                                       =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.in_full_norm_request);
                                     FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                       = false;
                                     FStar_TypeChecker_Cfg.nbe_step =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.nbe_step);
                                     FStar_TypeChecker_Cfg.for_extraction =
                                       (uu___3563_89061.FStar_TypeChecker_Cfg.for_extraction)
                                   });
                                FStar_TypeChecker_Cfg.tcenv =
                                  (uu___3561_89058.FStar_TypeChecker_Cfg.tcenv);
                                FStar_TypeChecker_Cfg.debug =
                                  (uu___3561_89058.FStar_TypeChecker_Cfg.debug);
                                FStar_TypeChecker_Cfg.delta_level =
                                  (uu___3561_89058.FStar_TypeChecker_Cfg.delta_level);
                                FStar_TypeChecker_Cfg.primitive_steps =
                                  (uu___3561_89058.FStar_TypeChecker_Cfg.primitive_steps);
                                FStar_TypeChecker_Cfg.strong =
                                  (uu___3561_89058.FStar_TypeChecker_Cfg.strong);
                                FStar_TypeChecker_Cfg.memoize_lazy =
                                  (uu___3561_89058.FStar_TypeChecker_Cfg.memoize_lazy);
                                FStar_TypeChecker_Cfg.normalize_pure_lets =
                                  (uu___3561_89058.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                FStar_TypeChecker_Cfg.reifying =
                                  (uu___3561_89058.FStar_TypeChecker_Cfg.reifying)
                              }) scrutinee_env [] scrutinee
                         else scrutinee  in
                       let uu____89065 =
                         mk
                           (FStar_Syntax_Syntax.Tm_match
                              (scrutinee1, branches1)) r
                          in
                       rebuild cfg1 env1 stack1 uu____89065)
                       in
                    let rec is_cons head1 =
                      let uu____89091 =
                        let uu____89092 = FStar_Syntax_Subst.compress head1
                           in
                        uu____89092.FStar_Syntax_Syntax.n  in
                      match uu____89091 with
                      | FStar_Syntax_Syntax.Tm_uinst (h,uu____89097) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____89102 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____89104;
                            FStar_Syntax_Syntax.fv_delta = uu____89105;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor );_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____89107;
                            FStar_Syntax_Syntax.fv_delta = uu____89108;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____89109);_}
                          -> true
                      | uu____89117 -> false  in
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
                      let uu____89286 =
                        FStar_Syntax_Util.head_and_args scrutinee2  in
                      match uu____89286 with
                      | (head1,args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu____89383 ->
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
                                | uu____89425 ->
                                    let uu____89426 =
                                      let uu____89428 = is_cons head1  in
                                      Prims.op_Negation uu____89428  in
                                    FStar_Util.Inr uu____89426)
                           | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                               let uu____89457 =
                                 let uu____89458 =
                                   FStar_Syntax_Util.un_uinst head1  in
                                 uu____89458.FStar_Syntax_Syntax.n  in
                               (match uu____89457 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____89477 ->
                                    let uu____89478 =
                                      let uu____89480 = is_cons head1  in
                                      Prims.op_Negation uu____89480  in
                                    FStar_Util.Inr uu____89478))
                    
                    and matches_args out a p =
                      match (a, p) with
                      | ([],[]) -> FStar_Util.Inl out
                      | ((t2,uu____89571)::rest_a,(p1,uu____89574)::rest_p)
                          ->
                          let uu____89633 = matches_pat t2 p1  in
                          (match uu____89633 with
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu____89686 -> FStar_Util.Inr false
                     in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1,wopt,b)::rest ->
                          let uu____89809 = matches_pat scrutinee1 p1  in
                          (match uu____89809 with
                           | FStar_Util.Inr (false ) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true ) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu____89855  ->
                                     let uu____89856 =
                                       FStar_Syntax_Print.pat_to_string p1
                                        in
                                     let uu____89858 =
                                       let uu____89860 =
                                         FStar_List.map
                                           (fun uu____89872  ->
                                              match uu____89872 with
                                              | (uu____89878,t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s
                                          in
                                       FStar_All.pipe_right uu____89860
                                         (FStar_String.concat "; ")
                                        in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu____89856 uu____89858);
                                (let env0 = env1  in
                                 let env2 =
                                   FStar_List.fold_left
                                     (fun env2  ->
                                        fun uu____89914  ->
                                          match uu____89914 with
                                          | (bv,t2) ->
                                              let uu____89937 =
                                                let uu____89944 =
                                                  let uu____89947 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____89947
                                                   in
                                                let uu____89948 =
                                                  let uu____89949 =
                                                    let uu____89981 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2))
                                                       in
                                                    ([], t2, uu____89981,
                                                      false)
                                                     in
                                                  Clos uu____89949  in
                                                (uu____89944, uu____89948)
                                                 in
                                              uu____89937 :: env2) env1 s
                                    in
                                 let uu____90096 =
                                   guard_when_clause wopt b rest  in
                                 norm cfg1 env2 stack1 uu____90096)))
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
            (fun uu____90129  ->
               let uu____90130 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____90130);
          (let uu____90133 = is_nbe_request s  in
           if uu____90133
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____90139  ->
                   let uu____90140 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____90140);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____90146  ->
                   let uu____90147 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____90147);
              (let uu____90150 =
                 FStar_Util.record_time (fun uu____90157  -> nbe_eval c s t)
                  in
               match uu____90150 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____90166  ->
                         let uu____90167 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____90169 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____90167 uu____90169);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____90177  ->
                   let uu____90178 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____90178);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____90184  ->
                   let uu____90185 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____90185);
              (let uu____90188 =
                 FStar_Util.record_time (fun uu____90195  -> norm c [] [] t)
                  in
               match uu____90188 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____90210  ->
                         let uu____90211 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____90213 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____90211 uu____90213);
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
        let uu____90248 = FStar_TypeChecker_Cfg.config s e  in
        norm_comp uu____90248 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____90266 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____90266 [] u
  
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
        let uu____90292 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____90292  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____90299 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___3719_90318 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3719_90318.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3719_90318.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name
              cfg.FStar_TypeChecker_Cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____90325 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____90325
          then
            let ct1 =
              let uu____90329 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____90329 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____90336 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____90336
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3729_90343 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3729_90343.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3729_90343.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3729_90343.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev
                      cfg.FStar_TypeChecker_Cfg.tcenv c
                     in
                  let uu___3733_90345 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3733_90345.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3733_90345.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3733_90345.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3733_90345.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3736_90346 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3736_90346.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3736_90346.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____90349 -> c
  
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
        let uu____90369 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____90369  in
      let uu____90376 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____90376
      then
        let uu____90379 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____90379 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____90385  ->
                 let uu____90386 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____90386)
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
          (fun uu___3752_90403  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___3751_90406 ->
            ((let uu____90408 =
                let uu____90414 =
                  let uu____90416 = FStar_Util.message_of_exn uu___3751_90406
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____90416
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____90414)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____90408);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          (fun uu___3762_90435  ->
             match () with
             | () ->
                 let uu____90436 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____90436 [] c) ()
        with
        | uu___3761_90445 ->
            ((let uu____90447 =
                let uu____90453 =
                  let uu____90455 = FStar_Util.message_of_exn uu___3761_90445
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____90455
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____90453)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____90447);
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
                   let uu____90504 =
                     let uu____90505 =
                       let uu____90512 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____90512)  in
                     FStar_Syntax_Syntax.Tm_refine uu____90505  in
                   mk uu____90504 t01.FStar_Syntax_Syntax.pos
               | uu____90517 -> t2)
          | uu____90518 -> t2  in
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
        let uu____90612 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____90612 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____90649 ->
                 let uu____90658 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____90658 with
                  | (actuals,uu____90668,uu____90669) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____90689 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____90689 with
                         | (binders,args) ->
                             let uu____90700 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____90700
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
      | uu____90715 ->
          let uu____90716 = FStar_Syntax_Util.head_and_args t  in
          (match uu____90716 with
           | (head1,args) ->
               let uu____90759 =
                 let uu____90760 = FStar_Syntax_Subst.compress head1  in
                 uu____90760.FStar_Syntax_Syntax.n  in
               (match uu____90759 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____90781 =
                      let uu____90796 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____90796  in
                    (match uu____90781 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____90836 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___3832_90844 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3832_90844.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3832_90844.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3832_90844.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3832_90844.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3832_90844.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3832_90844.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3832_90844.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3832_90844.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3832_90844.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___3832_90844.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3832_90844.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3832_90844.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3832_90844.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3832_90844.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3832_90844.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3832_90844.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3832_90844.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3832_90844.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3832_90844.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3832_90844.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3832_90844.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3832_90844.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3832_90844.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3832_90844.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3832_90844.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3832_90844.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3832_90844.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3832_90844.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3832_90844.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3832_90844.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3832_90844.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3832_90844.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3832_90844.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3832_90844.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3832_90844.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___3832_90844.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3832_90844.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3832_90844.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3832_90844.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3832_90844.FStar_TypeChecker_Env.nbe)
                                 }) t
                               in
                            match uu____90836 with
                            | (uu____90847,ty,uu____90849) ->
                                eta_expand_with_type env t ty))
                | uu____90850 ->
                    let uu____90851 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___3839_90859 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3839_90859.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3839_90859.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3839_90859.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3839_90859.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3839_90859.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3839_90859.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3839_90859.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3839_90859.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3839_90859.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___3839_90859.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3839_90859.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3839_90859.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3839_90859.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3839_90859.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3839_90859.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3839_90859.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3839_90859.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3839_90859.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3839_90859.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3839_90859.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3839_90859.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3839_90859.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3839_90859.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3839_90859.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3839_90859.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3839_90859.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3839_90859.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3839_90859.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3839_90859.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3839_90859.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3839_90859.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3839_90859.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3839_90859.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3839_90859.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3839_90859.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___3839_90859.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3839_90859.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3839_90859.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3839_90859.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3839_90859.FStar_TypeChecker_Env.nbe)
                         }) t
                       in
                    (match uu____90851 with
                     | (uu____90862,ty,uu____90864) ->
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
      let uu___3851_90946 = x  in
      let uu____90947 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3851_90946.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3851_90946.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____90947
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____90950 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____90974 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____90975 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____90976 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____90977 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____90984 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____90985 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____90986 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3877_91020 = rc  in
          let uu____91021 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____91030 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3877_91020.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____91021;
            FStar_Syntax_Syntax.residual_flags = uu____91030
          }  in
        let uu____91033 =
          let uu____91034 =
            let uu____91053 = elim_delayed_subst_binders bs  in
            let uu____91062 = elim_delayed_subst_term t2  in
            let uu____91065 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____91053, uu____91062, uu____91065)  in
          FStar_Syntax_Syntax.Tm_abs uu____91034  in
        mk1 uu____91033
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____91102 =
          let uu____91103 =
            let uu____91118 = elim_delayed_subst_binders bs  in
            let uu____91127 = elim_delayed_subst_comp c  in
            (uu____91118, uu____91127)  in
          FStar_Syntax_Syntax.Tm_arrow uu____91103  in
        mk1 uu____91102
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____91146 =
          let uu____91147 =
            let uu____91154 = elim_bv bv  in
            let uu____91155 = elim_delayed_subst_term phi  in
            (uu____91154, uu____91155)  in
          FStar_Syntax_Syntax.Tm_refine uu____91147  in
        mk1 uu____91146
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____91186 =
          let uu____91187 =
            let uu____91204 = elim_delayed_subst_term t2  in
            let uu____91207 = elim_delayed_subst_args args  in
            (uu____91204, uu____91207)  in
          FStar_Syntax_Syntax.Tm_app uu____91187  in
        mk1 uu____91186
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3899_91279 = p  in
              let uu____91280 =
                let uu____91281 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____91281  in
              {
                FStar_Syntax_Syntax.v = uu____91280;
                FStar_Syntax_Syntax.p =
                  (uu___3899_91279.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3903_91283 = p  in
              let uu____91284 =
                let uu____91285 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____91285  in
              {
                FStar_Syntax_Syntax.v = uu____91284;
                FStar_Syntax_Syntax.p =
                  (uu___3903_91283.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3909_91292 = p  in
              let uu____91293 =
                let uu____91294 =
                  let uu____91301 = elim_bv x  in
                  let uu____91302 = elim_delayed_subst_term t0  in
                  (uu____91301, uu____91302)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____91294  in
              {
                FStar_Syntax_Syntax.v = uu____91293;
                FStar_Syntax_Syntax.p =
                  (uu___3909_91292.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3915_91327 = p  in
              let uu____91328 =
                let uu____91329 =
                  let uu____91343 =
                    FStar_List.map
                      (fun uu____91369  ->
                         match uu____91369 with
                         | (x,b) ->
                             let uu____91386 = elim_pat x  in
                             (uu____91386, b)) pats
                     in
                  (fv, uu____91343)  in
                FStar_Syntax_Syntax.Pat_cons uu____91329  in
              {
                FStar_Syntax_Syntax.v = uu____91328;
                FStar_Syntax_Syntax.p =
                  (uu___3915_91327.FStar_Syntax_Syntax.p)
              }
          | uu____91401 -> p  in
        let elim_branch uu____91425 =
          match uu____91425 with
          | (pat,wopt,t3) ->
              let uu____91451 = elim_pat pat  in
              let uu____91454 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____91457 = elim_delayed_subst_term t3  in
              (uu____91451, uu____91454, uu____91457)
           in
        let uu____91462 =
          let uu____91463 =
            let uu____91486 = elim_delayed_subst_term t2  in
            let uu____91489 = FStar_List.map elim_branch branches  in
            (uu____91486, uu____91489)  in
          FStar_Syntax_Syntax.Tm_match uu____91463  in
        mk1 uu____91462
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____91620 =
          match uu____91620 with
          | (tc,topt) ->
              let uu____91655 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____91665 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____91665
                | FStar_Util.Inr c ->
                    let uu____91667 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____91667
                 in
              let uu____91668 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____91655, uu____91668)
           in
        let uu____91677 =
          let uu____91678 =
            let uu____91705 = elim_delayed_subst_term t2  in
            let uu____91708 = elim_ascription a  in
            (uu____91705, uu____91708, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____91678  in
        mk1 uu____91677
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3945_91771 = lb  in
          let uu____91772 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____91775 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3945_91771.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3945_91771.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____91772;
            FStar_Syntax_Syntax.lbeff =
              (uu___3945_91771.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____91775;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3945_91771.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3945_91771.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____91778 =
          let uu____91779 =
            let uu____91793 =
              let uu____91801 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____91801)  in
            let uu____91813 = elim_delayed_subst_term t2  in
            (uu____91793, uu____91813)  in
          FStar_Syntax_Syntax.Tm_let uu____91779  in
        mk1 uu____91778
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____91858 =
          let uu____91859 =
            let uu____91866 = elim_delayed_subst_term tm  in
            (uu____91866, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____91859  in
        mk1 uu____91858
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____91877 =
          let uu____91878 =
            let uu____91885 = elim_delayed_subst_term t2  in
            let uu____91888 = elim_delayed_subst_meta md  in
            (uu____91885, uu____91888)  in
          FStar_Syntax_Syntax.Tm_meta uu____91878  in
        mk1 uu____91877

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
      (fun uu___603_91897  ->
         match uu___603_91897 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____91901 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____91901
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
        let uu____91924 =
          let uu____91925 =
            let uu____91934 = elim_delayed_subst_term t  in
            (uu____91934, uopt)  in
          FStar_Syntax_Syntax.Total uu____91925  in
        mk1 uu____91924
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____91951 =
          let uu____91952 =
            let uu____91961 = elim_delayed_subst_term t  in
            (uu____91961, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____91952  in
        mk1 uu____91951
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3978_91970 = ct  in
          let uu____91971 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____91974 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____91985 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3978_91970.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3978_91970.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____91971;
            FStar_Syntax_Syntax.effect_args = uu____91974;
            FStar_Syntax_Syntax.flags = uu____91985
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___604_91988  ->
    match uu___604_91988 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____92002 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____92002
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____92041 =
          let uu____92048 = elim_delayed_subst_term t  in (m, uu____92048)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____92041
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____92060 =
          let uu____92069 = elim_delayed_subst_term t  in
          (m1, m2, uu____92069)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____92060
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
      (fun uu____92102  ->
         match uu____92102 with
         | (t,q) ->
             let uu____92121 = elim_delayed_subst_term t  in (uu____92121, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____92149  ->
         match uu____92149 with
         | (x,q) ->
             let uu____92168 =
               let uu___4002_92169 = x  in
               let uu____92170 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___4002_92169.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___4002_92169.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____92170
               }  in
             (uu____92168, q)) bs

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
            | (uu____92278,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____92310,FStar_Util.Inl t) ->
                let uu____92332 =
                  let uu____92339 =
                    let uu____92340 =
                      let uu____92355 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____92355)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____92340  in
                  FStar_Syntax_Syntax.mk uu____92339  in
                uu____92332 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____92371 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____92371 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____92403 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____92476 ->
                    let uu____92477 =
                      let uu____92486 =
                        let uu____92487 = FStar_Syntax_Subst.compress t4  in
                        uu____92487.FStar_Syntax_Syntax.n  in
                      (uu____92486, tc)  in
                    (match uu____92477 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____92516) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____92563) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____92608,FStar_Util.Inl uu____92609) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____92640 -> failwith "Impossible")
                 in
              (match uu____92403 with
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
          let uu____92779 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____92779 with
          | (univ_names1,binders1,tc) ->
              let uu____92853 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____92853)
  
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
          let uu____92907 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____92907 with
          | (univ_names1,binders1,tc) ->
              let uu____92981 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____92981)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____93023 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____93023 with
           | (univ_names1,binders1,typ1) ->
               let uu___4085_93063 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4085_93063.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4085_93063.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4085_93063.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4085_93063.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___4091_93078 = s  in
          let uu____93079 =
            let uu____93080 =
              let uu____93089 = FStar_List.map (elim_uvars env) sigs  in
              (uu____93089, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____93080  in
          {
            FStar_Syntax_Syntax.sigel = uu____93079;
            FStar_Syntax_Syntax.sigrng =
              (uu___4091_93078.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___4091_93078.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___4091_93078.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___4091_93078.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____93108 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____93108 with
           | (univ_names1,uu____93132,typ1) ->
               let uu___4105_93154 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4105_93154.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4105_93154.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4105_93154.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4105_93154.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____93161 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____93161 with
           | (univ_names1,uu____93185,typ1) ->
               let uu___4116_93207 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4116_93207.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4116_93207.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4116_93207.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4116_93207.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____93237 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____93237 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____93262 =
                            let uu____93263 =
                              let uu____93264 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____93264  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____93263
                             in
                          elim_delayed_subst_term uu____93262  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___4132_93267 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___4132_93267.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___4132_93267.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___4132_93267.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___4132_93267.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___4135_93268 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___4135_93268.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___4135_93268.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___4135_93268.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___4135_93268.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___4139_93275 = s  in
          let uu____93276 =
            let uu____93277 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____93277  in
          {
            FStar_Syntax_Syntax.sigel = uu____93276;
            FStar_Syntax_Syntax.sigrng =
              (uu___4139_93275.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___4139_93275.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___4139_93275.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___4139_93275.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____93281 = elim_uvars_aux_t env us [] t  in
          (match uu____93281 with
           | (us1,uu____93305,t1) ->
               let uu___4150_93327 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4150_93327.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4150_93327.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4150_93327.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4150_93327.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____93328 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____93331 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____93331 with
           | (univs1,binders,signature) ->
               let uu____93371 =
                 let uu____93376 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____93376 with
                 | (univs_opening,univs2) ->
                     let uu____93399 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____93399)
                  in
               (match uu____93371 with
                | (univs_opening,univs_closing) ->
                    let uu____93402 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____93408 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____93409 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____93408, uu____93409)  in
                    (match uu____93402 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____93435 =
                           match uu____93435 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____93453 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____93453 with
                                | (us1,t1) ->
                                    let uu____93464 =
                                      let uu____93473 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____93484 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____93473, uu____93484)  in
                                    (match uu____93464 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____93513 =
                                           let uu____93522 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____93533 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____93522, uu____93533)  in
                                         (match uu____93513 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____93563 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____93563
                                                 in
                                              let uu____93564 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____93564 with
                                               | (uu____93591,uu____93592,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____93615 =
                                                       let uu____93616 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____93616
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____93615
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____93625 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____93625 with
                           | (uu____93644,uu____93645,t1) -> t1  in
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
                             | uu____93721 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____93748 =
                               let uu____93749 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____93749.FStar_Syntax_Syntax.n  in
                             match uu____93748 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____93808 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____93842 =
                               let uu____93843 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____93843.FStar_Syntax_Syntax.n  in
                             match uu____93842 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____93866) ->
                                 let uu____93891 = destruct_action_body body
                                    in
                                 (match uu____93891 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____93940 ->
                                 let uu____93941 = destruct_action_body t  in
                                 (match uu____93941 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____93996 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____93996 with
                           | (action_univs,t) ->
                               let uu____94005 = destruct_action_typ_templ t
                                  in
                               (match uu____94005 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___4236_94052 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___4236_94052.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___4236_94052.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___4239_94054 = ed  in
                           let uu____94055 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____94056 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____94057 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____94058 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____94059 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____94060 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____94061 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____94062 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____94063 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____94064 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____94065 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____94066 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____94067 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____94068 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___4239_94054.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___4239_94054.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____94055;
                             FStar_Syntax_Syntax.bind_wp = uu____94056;
                             FStar_Syntax_Syntax.if_then_else = uu____94057;
                             FStar_Syntax_Syntax.ite_wp = uu____94058;
                             FStar_Syntax_Syntax.stronger = uu____94059;
                             FStar_Syntax_Syntax.close_wp = uu____94060;
                             FStar_Syntax_Syntax.assert_p = uu____94061;
                             FStar_Syntax_Syntax.assume_p = uu____94062;
                             FStar_Syntax_Syntax.null_wp = uu____94063;
                             FStar_Syntax_Syntax.trivial = uu____94064;
                             FStar_Syntax_Syntax.repr = uu____94065;
                             FStar_Syntax_Syntax.return_repr = uu____94066;
                             FStar_Syntax_Syntax.bind_repr = uu____94067;
                             FStar_Syntax_Syntax.actions = uu____94068;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___4239_94054.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___4242_94071 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___4242_94071.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___4242_94071.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___4242_94071.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___4242_94071.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___605_94092 =
            match uu___605_94092 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____94123 = elim_uvars_aux_t env us [] t  in
                (match uu____94123 with
                 | (us1,uu____94155,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___4257_94186 = sub_eff  in
            let uu____94187 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____94190 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___4257_94186.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___4257_94186.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____94187;
              FStar_Syntax_Syntax.lift = uu____94190
            }  in
          let uu___4260_94193 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___4260_94193.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___4260_94193.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___4260_94193.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___4260_94193.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____94203 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____94203 with
           | (univ_names1,binders1,comp1) ->
               let uu___4273_94243 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4273_94243.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4273_94243.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4273_94243.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4273_94243.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____94246 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____94247 -> s
  
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
        let uu____94296 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____94296 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____94318 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____94318 with
             | (uu____94325,head_def) ->
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
      let uu____94331 = FStar_Syntax_Util.head_and_args t  in
      match uu____94331 with
      | (head1,args) ->
          let uu____94376 =
            let uu____94377 = FStar_Syntax_Subst.compress head1  in
            uu____94377.FStar_Syntax_Syntax.n  in
          (match uu____94376 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____94384;
                  FStar_Syntax_Syntax.vars = uu____94385;_},us)
               -> aux fv us args
           | uu____94391 -> FStar_Pervasives_Native.None)
  