open Prims
let cases :
  'Auu____63967 'Auu____63968 .
    ('Auu____63967 -> 'Auu____63968) ->
      'Auu____63968 ->
        'Auu____63967 FStar_Pervasives_Native.option -> 'Auu____63968
  =
  fun f  ->
    fun d  ->
      fun uu___585_63988  ->
        match uu___585_63988 with
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
    match projectee with | Clos _0 -> true | uu____64086 -> false
  
let (__proj__Clos__item___0 :
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
      Prims.list * FStar_Syntax_Syntax.term * ((FStar_Syntax_Syntax.binder
      FStar_Pervasives_Native.option * closure) Prims.list *
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool))
  = fun projectee  -> match projectee with | Clos _0 -> _0 
let (uu___is_Univ : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____64199 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____64218 -> false
  
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
    match projectee with | Arg _0 -> true | uu____64398 -> false
  
let (__proj__Arg__item___0 :
  stack_elt -> (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)) =
  fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____64442 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range))
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____64486 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo) =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____64565 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env * branches * FStar_TypeChecker_Cfg.cfg * FStar_Range.range))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____64621 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * env *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
      FStar_Range.range))
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____64685 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Range.range))
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____64735 -> false
  
let (__proj__Meta__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.metadata * FStar_Range.range)) =
  fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____64781 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding *
      FStar_Range.range))
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____64825 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> FStar_TypeChecker_Cfg.cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____64849 -> false
  
let (__proj__Debug__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.term * FStar_Util.time)) =
  fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____64879 = FStar_Syntax_Util.head_and_args' t  in
    match uu____64879 with | (hd1,uu____64895) -> hd1
  
let mk :
  'Auu____64923 .
    'Auu____64923 ->
      FStar_Range.range -> 'Auu____64923 FStar_Syntax_Syntax.syntax
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
          let uu____64988 = FStar_ST.op_Bang r  in
          match uu____64988 with
          | FStar_Pervasives_Native.Some uu____65036 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____65113 =
      FStar_List.map
        (fun uu____65129  ->
           match uu____65129 with
           | (bopt,c) ->
               let uu____65143 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____65148 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____65143 uu____65148) env
       in
    FStar_All.pipe_right uu____65113 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___586_65156  ->
    match uu___586_65156 with
    | Clos (env,t,uu____65160,uu____65161) ->
        let uu____65208 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____65218 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____65208 uu____65218
    | Univ uu____65221 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___587_65230  ->
    match uu___587_65230 with
    | Arg (c,uu____65233,uu____65234) ->
        let uu____65235 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____65235
    | MemoLazy uu____65238 -> "MemoLazy"
    | Abs (uu____65246,bs,uu____65248,uu____65249,uu____65250) ->
        let uu____65255 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____65255
    | UnivArgs uu____65266 -> "UnivArgs"
    | Match uu____65274 -> "Match"
    | App (uu____65284,t,uu____65286,uu____65287) ->
        let uu____65288 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____65288
    | Meta (uu____65291,m,uu____65293) -> "Meta"
    | Let uu____65295 -> "Let"
    | Cfg uu____65305 -> "Cfg"
    | Debug (t,uu____65308) ->
        let uu____65309 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____65309
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____65323 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____65323 (FStar_String.concat "; ")
  
let is_empty : 'Auu____65338 . 'Auu____65338 Prims.list -> Prims.bool =
  fun uu___588_65346  ->
    match uu___588_65346 with | [] -> true | uu____65350 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        (fun uu___700_65383  ->
           match () with
           | () ->
               let uu____65384 =
                 FStar_List.nth env x.FStar_Syntax_Syntax.index  in
               FStar_Pervasives_Native.snd uu____65384) ()
      with
      | uu___699_65401 ->
          let uu____65402 =
            let uu____65404 = FStar_Syntax_Print.db_to_string x  in
            let uu____65406 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____65404
              uu____65406
             in
          failwith uu____65402
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____65417 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____65417
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____65424 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____65424
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____65431 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____65431
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
          let uu____65469 =
            FStar_List.fold_left
              (fun uu____65495  ->
                 fun u1  ->
                   match uu____65495 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____65520 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____65520 with
                        | (k_u,n1) ->
                            let uu____65538 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____65538
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____65469 with
          | (uu____65559,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 (fun uu___734_65585  ->
                    match () with
                    | () ->
                        let uu____65588 =
                          let uu____65589 = FStar_List.nth env x  in
                          FStar_Pervasives_Native.snd uu____65589  in
                        (match uu____65588 with
                         | Univ u3 ->
                             ((let uu____65608 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      cfg.FStar_TypeChecker_Cfg.tcenv)
                                   (FStar_Options.Other "univ_norm")
                                  in
                               if uu____65608
                               then
                                 let uu____65613 =
                                   FStar_Syntax_Print.univ_to_string u3  in
                                 FStar_Util.print1
                                   "Univ (in norm_universe): %s\n"
                                   uu____65613
                               else ());
                              aux u3)
                         | Dummy  -> [u2]
                         | uu____65618 ->
                             let uu____65619 =
                               let uu____65621 = FStar_Util.string_of_int x
                                  in
                               FStar_Util.format1
                                 "Impossible: universe variable u@%s bound to a term"
                                 uu____65621
                                in
                             failwith uu____65619)) ()
               with
               | uu____65631 ->
                   if
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else
                     (let uu____65637 =
                        let uu____65639 = FStar_Util.string_of_int x  in
                        FStar_String.op_Hat "Universe variable not found: u@"
                          uu____65639
                         in
                      failwith uu____65637))
          | FStar_Syntax_Syntax.U_unif uu____65644 when
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____65653 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____65662 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____65669 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____65669 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____65686 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____65686 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____65697 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____65707 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____65707 with
                                  | (uu____65714,m) -> n1 <= m))
                           in
                        if uu____65697 then rest1 else us1
                    | uu____65723 -> us1)
               | uu____65729 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____65733 = aux u3  in
              FStar_List.map
                (fun _65736  -> FStar_Syntax_Syntax.U_succ _65736)
                uu____65733
           in
        if
          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____65740 = aux u  in
           match uu____65740 with
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
            (fun uu____65909  ->
               let uu____65910 = FStar_Syntax_Print.tag_of_term t  in
               let uu____65912 = env_to_string env  in
               let uu____65914 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____65910 uu____65912 uu____65914);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____65927 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____65930 ->
                    let uu____65953 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____65953
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____65954 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____65955 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____65956 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____65957 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____65982 ->
                           let uu____65995 =
                             let uu____65997 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____65999 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____65997 uu____65999
                              in
                           failwith uu____65995
                       | uu____66004 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___589_66040  ->
                                         match uu___589_66040 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____66047 =
                                               let uu____66054 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____66054)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____66047
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___828_66066 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___828_66066.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___828_66066.FStar_Syntax_Syntax.sort)
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
                                              | uu____66072 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____66075 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___837_66080 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___837_66080.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___837_66080.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____66101 =
                        let uu____66102 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____66102  in
                      mk uu____66101 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____66110 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____66110  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____66112 = lookup_bvar env x  in
                    (match uu____66112 with
                     | Univ uu____66115 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___853_66120 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___853_66120.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___853_66120.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____66126,uu____66127) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____66218  ->
                              fun stack1  ->
                                match uu____66218 with
                                | (a,aq) ->
                                    let uu____66230 =
                                      let uu____66231 =
                                        let uu____66238 =
                                          let uu____66239 =
                                            let uu____66271 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____66271, false)  in
                                          Clos uu____66239  in
                                        (uu____66238, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____66231  in
                                    uu____66230 :: stack1) args)
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
                    let uu____66461 = close_binders cfg env bs  in
                    (match uu____66461 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,uu____66511) when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    ->
                    inline_closure_env cfg env stack
                      x.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____66522 =
                      let uu____66535 =
                        let uu____66544 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____66544]  in
                      close_binders cfg env uu____66535  in
                    (match uu____66522 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____66589 =
                             let uu____66590 =
                               let uu____66597 =
                                 let uu____66598 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____66598
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____66597, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____66590  in
                           mk uu____66589 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____66697 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____66697
                      | FStar_Util.Inr c ->
                          let uu____66711 = close_comp cfg env c  in
                          FStar_Util.Inr uu____66711
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____66730 =
                        let uu____66731 =
                          let uu____66758 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____66758, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____66731  in
                      mk uu____66730 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____66804 =
                            let uu____66805 =
                              let uu____66812 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____66812, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____66805  in
                          mk uu____66804 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____66867  -> dummy :: env1) env
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
                    let uu____66888 =
                      let uu____66899 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____66899
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____66921 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___945_66937 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___945_66937.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___945_66937.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____66921))
                       in
                    (match uu____66888 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___950_66955 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___950_66955.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___950_66955.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___950_66955.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___950_66955.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____66972,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____67038  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____67055 =
                          FStar_Syntax_Syntax.is_top_level lbs  in
                        if uu____67055
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____67070  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____67094 =
                          FStar_Syntax_Syntax.is_top_level lbs  in
                        if uu____67094
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___973_67105 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___973_67105.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___973_67105.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___976_67106 = lb  in
                      let uu____67107 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___976_67106.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___976_67106.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____67107;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___976_67106.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___976_67106.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____67139  -> fun env1  -> dummy :: env1)
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
            (fun uu____67231  ->
               let uu____67232 = FStar_Syntax_Print.tag_of_term t  in
               let uu____67234 = env_to_string env  in
               let uu____67236 = stack_to_string stack  in
               let uu____67238 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____67232 uu____67234 uu____67236 uu____67238);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____67245,uu____67246),aq,r))::stack1
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
               let uu____67327 = close_binders cfg env' bs  in
               (match uu____67327 with
                | (bs1,uu____67343) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____67363 =
                      let uu___1034_67366 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___1034_67366.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___1034_67366.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____67363)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____67422 =
                 match uu____67422 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____67537 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____67568 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____67657  ->
                                     fun uu____67658  ->
                                       match (uu____67657, uu____67658) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____67808 = norm_pat env4 p1
                                              in
                                           (match uu____67808 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____67568 with
                            | (pats1,env4) ->
                                ((let uu___1071_67978 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___1071_67978.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___1075_67999 = x  in
                             let uu____68000 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1075_67999.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1075_67999.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____68000
                             }  in
                           ((let uu___1078_68014 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___1078_68014.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___1082_68025 = x  in
                             let uu____68026 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1082_68025.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1082_68025.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____68026
                             }  in
                           ((let uu___1085_68040 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___1085_68040.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___1091_68056 = x  in
                             let uu____68057 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1091_68056.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1091_68056.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____68057
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___1095_68074 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___1095_68074.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____68079 = norm_pat env2 pat  in
                     (match uu____68079 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____68148 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____68148
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____68167 =
                   let uu____68168 =
                     let uu____68191 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____68191)  in
                   FStar_Syntax_Syntax.Tm_match uu____68168  in
                 mk uu____68167 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____68306 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____68415  ->
                                       match uu____68415 with
                                       | (a,q) ->
                                           let uu____68442 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____68442, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____68306
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____68455 =
                       let uu____68462 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____68462)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____68455
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____68474 =
                       let uu____68483 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____68483)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____68474
                 | uu____68488 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____68494 -> failwith "Impossible: unexpected stack element")

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
            let uu____68510 =
              let uu____68511 = inline_closure_env cfg env [] t  in
              FStar_Syntax_Syntax.Meta uu____68511  in
            FStar_Pervasives_Native.Some uu____68510
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
        let uu____68528 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____68612  ->
                  fun uu____68613  ->
                    match (uu____68612, uu____68613) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___1148_68753 = b  in
                          let uu____68754 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1148_68753.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1148_68753.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____68754
                          }  in
                        let imp1 = close_imp cfg env1 imp  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp1) :: out))) (env, []))
           in
        match uu____68528 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____68896 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____68909 = inline_closure_env cfg env [] t  in
                 let uu____68910 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____68909 uu____68910
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____68923 = inline_closure_env cfg env [] t  in
                 let uu____68924 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____68923 uu____68924
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____68978  ->
                           match uu____68978 with
                           | (a,q) ->
                               let uu____68999 =
                                 inline_closure_env cfg env [] a  in
                               (uu____68999, q)))
                    in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___590_69016  ->
                           match uu___590_69016 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____69020 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____69020
                           | f -> f))
                    in
                 let uu____69024 =
                   let uu___1181_69025 = c1  in
                   let uu____69026 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____69026;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___1181_69025.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____69024)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___591_69036  ->
            match uu___591_69036 with
            | FStar_Syntax_Syntax.DECREASES uu____69038 -> false
            | uu____69042 -> true))

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
                   (fun uu___592_69061  ->
                      match uu___592_69061 with
                      | FStar_Syntax_Syntax.DECREASES uu____69063 -> false
                      | uu____69067 -> true))
               in
            let rc1 =
              let uu___1198_69070 = rc  in
              let uu____69071 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___1198_69070.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____69071;
                FStar_Syntax_Syntax.residual_flags = flags
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____69080 -> lopt

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
    let uu____69150 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____69150 with
    | FStar_Pervasives_Native.Some e ->
        let uu____69189 = FStar_Syntax_Embeddings.unembed e t  in
        uu____69189 true FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____69213 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv * 'Auu____69213)
        FStar_Pervasives_Native.option * closure) Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____69275  ->
           fun subst1  ->
             match uu____69275 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____69316,uu____69317)) ->
                      let uu____69378 = b  in
                      (match uu____69378 with
                       | (bv,uu____69386) ->
                           let uu____69387 =
                             let uu____69389 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____69389  in
                           if uu____69387
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____69397 = unembed_binder term1  in
                              match uu____69397 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____69404 =
                                      let uu___1233_69405 = bv  in
                                      let uu____69406 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___1233_69405.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___1233_69405.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____69406
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____69404
                                     in
                                  let b_for_x =
                                    let uu____69412 =
                                      let uu____69419 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____69419)
                                       in
                                    FStar_Syntax_Syntax.NT uu____69412  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___593_69435  ->
                                         match uu___593_69435 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____69437,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____69439;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____69440;_})
                                             ->
                                             let uu____69445 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____69445
                                         | uu____69447 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____69449 -> subst1)) env []
  
let reduce_primops :
  'Auu____69472 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'Auu____69472)
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
            (let uu____69526 = FStar_Syntax_Util.head_and_args tm  in
             match uu____69526 with
             | (head1,args) ->
                 let uu____69571 =
                   let uu____69572 = FStar_Syntax_Util.un_uinst head1  in
                   uu____69572.FStar_Syntax_Syntax.n  in
                 (match uu____69571 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____69578 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                      (match uu____69578 with
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
                                (fun uu____69607  ->
                                   let uu____69608 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name
                                      in
                                   let uu____69610 =
                                     FStar_Util.string_of_int l  in
                                   let uu____69618 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____69608 uu____69610 uu____69618);
                              tm)
                           else
                             (let uu____69623 =
                                if l = prim_step.FStar_TypeChecker_Cfg.arity
                                then (args, [])
                                else
                                  FStar_List.splitAt
                                    prim_step.FStar_TypeChecker_Cfg.arity
                                    args
                                 in
                              match uu____69623 with
                              | (args_1,args_2) ->
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____69713  ->
                                        let uu____69714 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____69714);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____69719  ->
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
                                           (fun uu____69735  ->
                                              let uu____69736 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____69736);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____69744  ->
                                              let uu____69745 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____69747 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____69745 uu____69747);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____69750 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____69754  ->
                                 let uu____69755 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____69755);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____69761  ->
                            let uu____69762 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____69762);
                       (match args with
                        | (a1,uu____69768)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____69793 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____69807  ->
                            let uu____69808 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____69808);
                       (match args with
                        | (t,uu____69814)::(r,uu____69816)::[] ->
                            let uu____69857 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____69857 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____69863 -> tm))
                  | uu____69874 -> tm))
  
let reduce_equality :
  'Auu____69886 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'Auu____69886)
          FStar_Pervasives_Native.option * closure) Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun tm  ->
        reduce_primops norm_cb
          (let uu___1321_69939 = cfg  in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___1323_69942 = FStar_TypeChecker_Cfg.default_steps  in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.nbe_step);
                  FStar_TypeChecker_Cfg.for_extraction =
                    (uu___1323_69942.FStar_TypeChecker_Cfg.for_extraction)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___1321_69939.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___1321_69939.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___1321_69939.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___1321_69939.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___1321_69939.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___1321_69939.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___1321_69939.FStar_TypeChecker_Cfg.reifying)
           }) tm
  
type norm_request_t =
  | Norm_request_none 
  | Norm_request_ready 
  | Norm_request_requires_rejig 
let (uu___is_Norm_request_none : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_none  -> true | uu____69953 -> false
  
let (uu___is_Norm_request_ready : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_ready  -> true | uu____69964 -> false
  
let (uu___is_Norm_request_requires_rejig : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Norm_request_requires_rejig  -> true
    | uu____69975 -> false
  
let (is_norm_request :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.args -> norm_request_t) =
  fun hd1  ->
    fun args  ->
      let aux min_args =
        let uu____69996 = FStar_All.pipe_right args FStar_List.length  in
        FStar_All.pipe_right uu____69996
          (fun n1  ->
             if n1 < min_args
             then Norm_request_none
             else
               if n1 = min_args
               then Norm_request_ready
               else Norm_request_requires_rejig)
         in
      let uu____70028 =
        let uu____70029 = FStar_Syntax_Util.un_uinst hd1  in
        uu____70029.FStar_Syntax_Syntax.n  in
      match uu____70028 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          -> aux (Prims.parse_int "2")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          aux (Prims.parse_int "1")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          aux (Prims.parse_int "3")
      | uu____70038 -> Norm_request_none
  
let (should_consider_norm_requests : FStar_TypeChecker_Cfg.cfg -> Prims.bool)
  =
  fun cfg  ->
    (Prims.op_Negation
       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
      &&
      (let uu____70047 =
         FStar_Ident.lid_equals
           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
           FStar_Parser_Const.prims_lid
          in
       Prims.op_Negation uu____70047)
  
let (rejig_norm_request :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term)
  =
  fun hd1  ->
    fun args  ->
      let uu____70060 =
        let uu____70061 = FStar_Syntax_Util.un_uinst hd1  in
        uu____70061.FStar_Syntax_Syntax.n  in
      match uu____70060 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          ->
          (match args with
           | t1::t2::rest when
               (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____70119 = FStar_Syntax_Util.mk_app hd1 [t1; t2]  in
               FStar_Syntax_Util.mk_app uu____70119 rest
           | uu____70146 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize_term")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          (match args with
           | t::rest when (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____70186 = FStar_Syntax_Util.mk_app hd1 [t]  in
               FStar_Syntax_Util.mk_app uu____70186 rest
           | uu____70205 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          (match args with
           | t1::t2::t3::rest when
               (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____70279 = FStar_Syntax_Util.mk_app hd1 [t1; t2; t3]
                  in
               FStar_Syntax_Util.mk_app uu____70279 rest
           | uu____70314 ->
               failwith "Impossible! invalid rejig_norm_request for norm")
      | uu____70316 ->
          let uu____70317 =
            let uu____70319 = FStar_Syntax_Print.term_to_string hd1  in
            FStar_String.op_Hat
              "Impossible! invalid rejig_norm_request for: %s" uu____70319
             in
          failwith uu____70317
  
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s  ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
  
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___594_70340  ->
    match uu___594_70340 with
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
        let uu____70347 =
          let uu____70350 =
            let uu____70351 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            FStar_TypeChecker_Env.UnfoldOnly uu____70351  in
          [uu____70350]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____70347
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____70359 =
          let uu____70362 =
            let uu____70363 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            FStar_TypeChecker_Env.UnfoldFully uu____70363  in
          [uu____70362]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____70359
    | FStar_Syntax_Embeddings.UnfoldAttr names1 ->
        let uu____70371 =
          let uu____70374 =
            let uu____70375 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            FStar_TypeChecker_Env.UnfoldAttr uu____70375  in
          [uu____70374]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____70371
    | FStar_Syntax_Embeddings.NBE  -> [FStar_TypeChecker_Env.NBE]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  = fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____70400 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term * 'Auu____70400) Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list * FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____70451 =
            let uu____70456 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____70456 s  in
          match uu____70451 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____70472 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____70472
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
        | uu____70507::(tm,uu____70509)::[] ->
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
        | (tm,uu____70538)::[] ->
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
        | (steps,uu____70559)::uu____70560::(tm,uu____70562)::[] ->
            let add_exclude s z =
              let uu____70600 =
                FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s  in
              if uu____70600
              then s
              else (FStar_TypeChecker_Env.Exclude z) :: s  in
            let uu____70607 =
              let uu____70612 = full_norm steps  in parse_steps uu____70612
               in
            (match uu____70607 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = FStar_TypeChecker_Env.Beta :: s  in
                 let s2 = add_exclude s1 FStar_TypeChecker_Env.Zeta  in
                 let s3 = add_exclude s2 FStar_TypeChecker_Env.Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____70651 -> FStar_Pervasives_Native.None
  
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun s  ->
      fun tm  ->
        let delta_level =
          let uu____70683 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___595_70690  ->
                    match uu___595_70690 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____70692 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____70694 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____70698 -> true
                    | uu____70702 -> false))
             in
          if uu____70683
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta]  in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____70712  ->
             let uu____70713 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____70713);
        (let tm_norm =
           let uu____70717 =
             let uu____70732 = FStar_TypeChecker_Cfg.cfg_env cfg  in
             uu____70732.FStar_TypeChecker_Env.nbe  in
           uu____70717 s cfg.FStar_TypeChecker_Cfg.tcenv tm  in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____70736  ->
              let uu____70737 = FStar_Syntax_Print.term_to_string tm_norm  in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____70737);
         tm_norm)
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___596_70748  ->
    match uu___596_70748 with
    | (App
        (uu____70752,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____70753;
                       FStar_Syntax_Syntax.vars = uu____70754;_},uu____70755,uu____70756))::uu____70757
        -> true
    | uu____70763 -> false
  
let firstn :
  'Auu____70774 .
    Prims.int ->
      'Auu____70774 Prims.list ->
        ('Auu____70774 Prims.list * 'Auu____70774 Prims.list)
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack  ->
      let rec drop_irrel uu___597_70831 =
        match uu___597_70831 with
        | (MemoLazy uu____70836)::s -> drop_irrel s
        | (UnivArgs uu____70846)::s -> drop_irrel s
        | s -> s  in
      let uu____70859 = drop_irrel stack  in
      match uu____70859 with
      | (App
          (uu____70863,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____70864;
                         FStar_Syntax_Syntax.vars = uu____70865;_},uu____70866,uu____70867))::uu____70868
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____70873 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____70902) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____70912) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____70933  ->
                  match uu____70933 with
                  | (a,uu____70944) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____70955 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____70980 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____70982 -> false
    | FStar_Syntax_Syntax.Tm_type uu____70996 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____70998 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____71000 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____71002 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____71004 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____71007 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____71015 -> false
    | FStar_Syntax_Syntax.Tm_let uu____71023 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____71038 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____71058 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____71074 -> true
    | FStar_Syntax_Syntax.Tm_match uu____71082 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____71154  ->
                   match uu____71154 with
                   | (a,uu____71165) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____71176) ->
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
                     (fun uu____71308  ->
                        match uu____71308 with
                        | (a,uu____71319) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____71328,uu____71329,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____71335,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____71341 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____71351 -> false
            | FStar_Syntax_Syntax.Meta_named uu____71353 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____71364 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____71375 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Should_unfold_fully  -> true
    | uu____71386 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Should_unfold_reify  -> true
    | uu____71397 -> false
  
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
            let uu____71430 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo
               in
            match uu____71430 with
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
              (fun uu____71629  ->
                 fun uu____71630  ->
                   match (uu____71629, uu____71630) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____71736 =
            match uu____71736 with
            | (x,y,z) ->
                let uu____71756 = FStar_Util.string_of_bool x  in
                let uu____71758 = FStar_Util.string_of_bool y  in
                let uu____71760 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____71756 uu____71758
                  uu____71760
             in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg  in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____71788  ->
                    let uu____71789 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____71791 = FStar_Util.string_of_bool b  in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____71789 uu____71791);
               if b then reif else no)
            else
              if
                (let uu____71806 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                 FStar_Option.isSome uu____71806)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____71811  ->
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
                          ((is_rec,uu____71846),uu____71847);
                        FStar_Syntax_Syntax.sigrng = uu____71848;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____71850;
                        FStar_Syntax_Syntax.sigattrs = uu____71851;_},uu____71852),uu____71853),uu____71854,uu____71855,uu____71856)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____71963  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____71965,uu____71966,uu____71967,uu____71968) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____72035  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____72038),uu____72039);
                        FStar_Syntax_Syntax.sigrng = uu____72040;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____72042;
                        FStar_Syntax_Syntax.sigattrs = uu____72043;_},uu____72044),uu____72045),uu____72046,uu____72047,uu____72048)
                     when
                     is_rec &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____72155  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____72157,FStar_Pervasives_Native.Some
                    uu____72158,uu____72159,uu____72160) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____72228  ->
                           let uu____72229 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____72229);
                      (let uu____72232 =
                         let uu____72244 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____72270 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____72270
                            in
                         let uu____72282 =
                           let uu____72294 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____72320 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____72320
                              in
                           let uu____72336 =
                             let uu____72348 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____72374 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____72374
                                in
                             [uu____72348]  in
                           uu____72294 :: uu____72336  in
                         uu____72244 :: uu____72282  in
                       comb_or uu____72232))
                 | (uu____72422,uu____72423,FStar_Pervasives_Native.Some
                    uu____72424,uu____72425) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____72493  ->
                           let uu____72494 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____72494);
                      (let uu____72497 =
                         let uu____72509 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____72535 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____72535
                            in
                         let uu____72547 =
                           let uu____72559 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____72585 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____72585
                              in
                           let uu____72601 =
                             let uu____72613 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____72639 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____72639
                                in
                             [uu____72613]  in
                           uu____72559 :: uu____72601  in
                         uu____72509 :: uu____72547  in
                       comb_or uu____72497))
                 | (uu____72687,uu____72688,uu____72689,FStar_Pervasives_Native.Some
                    uu____72690) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____72758  ->
                           let uu____72759 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____72759);
                      (let uu____72762 =
                         let uu____72774 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____72800 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____72800
                            in
                         let uu____72812 =
                           let uu____72824 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____72850 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____72850
                              in
                           let uu____72866 =
                             let uu____72878 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____72904 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____72904
                                in
                             [uu____72878]  in
                           uu____72824 :: uu____72866  in
                         uu____72774 :: uu____72812  in
                       comb_or uu____72762))
                 | uu____72952 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____72998  ->
                           let uu____72999 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____73001 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____73003 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level
                              in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____72999 uu____73001 uu____73003);
                      (let uu____73006 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___598_73012  ->
                                 match uu___598_73012 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.InliningDelta  ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____73018 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv
                                        in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____73018 l))
                          in
                       FStar_All.pipe_left yesno uu____73006)))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____73034  ->
               let uu____73035 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____73037 =
                 let uu____73039 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____73039  in
               let uu____73040 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____73035 uu____73037 uu____73040);
          (match res with
           | (false ,uu____73043,uu____73044) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____73069 ->
               let uu____73079 =
                 let uu____73081 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____73081
                  in
               FStar_All.pipe_left failwith uu____73079)
  
let decide_unfolding :
  'Auu____73100 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'Auu____73100 ->
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
                    let uu___1740_73169 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___1742_73172 =
                           cfg.FStar_TypeChecker_Cfg.steps  in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1742_73172.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1742_73172.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1742_73172.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1742_73172.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1742_73172.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1742_73172.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1742_73172.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___1742_73172.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1742_73172.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1742_73172.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1742_73172.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1742_73172.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1742_73172.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1742_73172.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1742_73172.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1742_73172.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1742_73172.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1742_73172.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___1742_73172.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1742_73172.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1742_73172.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1742_73172.FStar_TypeChecker_Cfg.for_extraction)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1740_73169.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1740_73169.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___1740_73169.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1740_73169.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1740_73169.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1740_73169.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1740_73169.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1740_73169.FStar_TypeChecker_Cfg.reifying)
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
                        let uu____73234 = push1 e t  in (UnivArgs (us, r)) ::
                          uu____73234
                    | h::t -> e :: h :: t  in
                  let ref =
                    let uu____73246 =
                      let uu____73253 =
                        let uu____73254 =
                          let uu____73255 = FStar_Syntax_Syntax.lid_of_fv fv
                             in
                          FStar_Const.Const_reflect uu____73255  in
                        FStar_Syntax_Syntax.Tm_constant uu____73254  in
                      FStar_Syntax_Syntax.mk uu____73253  in
                    uu____73246 FStar_Pervasives_Native.None
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
    let uu____73324 =
      let uu____73325 = FStar_Syntax_Subst.compress t  in
      uu____73325.FStar_Syntax_Syntax.n  in
    match uu____73324 with
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____73356 =
          let uu____73357 = FStar_Syntax_Util.un_uinst hd1  in
          uu____73357.FStar_Syntax_Syntax.n  in
        (match uu____73356 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStar_List.length args) = (Prims.parse_int "3"))
             ->
             let f =
               let uu____73374 =
                 let uu____73381 =
                   let uu____73392 = FStar_All.pipe_right args FStar_List.tl
                      in
                   FStar_All.pipe_right uu____73392 FStar_List.tl  in
                 FStar_All.pipe_right uu____73381 FStar_List.hd  in
               FStar_All.pipe_right uu____73374 FStar_Pervasives_Native.fst
                in
             FStar_Pervasives_Native.Some f
         | uu____73491 -> FStar_Pervasives_Native.None)
    | uu____73492 -> FStar_Pervasives_Native.None
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____73771 ->
                   let uu____73794 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____73794
               | uu____73797 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____73807  ->
               let uu____73808 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____73810 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____73812 = FStar_Syntax_Print.term_to_string t1  in
               let uu____73814 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____73822 =
                 let uu____73824 =
                   let uu____73827 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____73827
                    in
                 stack_to_string uu____73824  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____73808 uu____73810 uu____73812 uu____73814 uu____73822);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____73855  ->
               let uu____73856 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____73856);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____73862  ->
                     let uu____73863 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____73863);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____73866 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____73870  ->
                     let uu____73871 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____73871);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____73874 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____73878  ->
                     let uu____73879 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____73879);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____73882 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____73886  ->
                     let uu____73887 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____73887);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____73890;
                 FStar_Syntax_Syntax.fv_delta = uu____73891;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____73895  ->
                     let uu____73896 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____73896);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____73899;
                 FStar_Syntax_Syntax.fv_delta = uu____73900;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____73901);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____73911  ->
                     let uu____73912 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____73912);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid
                  in
               let uu____73918 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
               (match uu____73918 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level _73921) when
                    _73921 = (Prims.parse_int "0") ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____73925  ->
                          let uu____73926 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____73926);
                     rebuild cfg env stack t1)
                | uu____73929 ->
                    let uu____73932 =
                      decide_unfolding cfg env stack
                        t1.FStar_Syntax_Syntax.pos fv qninfo
                       in
                    (match uu____73932 with
                     | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                         do_unfold_fv cfg1 env stack1 t1 qninfo fv
                     | FStar_Pervasives_Native.None  ->
                         rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_quoted uu____73959 ->
               let uu____73966 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____73966
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____73994 = is_norm_request hd1 args  in
                  uu____73994 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu____74000 = rejig_norm_request hd1 args  in
                 norm cfg env stack uu____74000))
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____74028 = is_norm_request hd1 args  in
                  uu____74028 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___1850_74035 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1852_74038 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1852_74038.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1852_74038.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1852_74038.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___1852_74038.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1852_74038.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1852_74038.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1852_74038.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1852_74038.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1852_74038.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1852_74038.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1852_74038.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1852_74038.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1852_74038.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1852_74038.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1852_74038.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1852_74038.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1852_74038.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1852_74038.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1852_74038.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1852_74038.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1852_74038.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1852_74038.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1852_74038.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1850_74035.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1850_74035.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1850_74035.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1850_74035.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1850_74035.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1850_74035.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____74045 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____74045 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____74081  ->
                                 fun stack1  ->
                                   match uu____74081 with
                                   | (a,aq) ->
                                       let uu____74093 =
                                         let uu____74094 =
                                           let uu____74101 =
                                             let uu____74102 =
                                               let uu____74134 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____74134, false)
                                                in
                                             Clos uu____74102  in
                                           (uu____74101, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____74094  in
                                       uu____74093 :: stack1) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____74224  ->
                            let uu____74225 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____74225);
                       norm cfg env stack1 hd1))
                 | FStar_Pervasives_Native.Some (s,tm) when is_nbe_request s
                     ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____74252 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting NBE request on %s ... \n" uu____74252)
                      else ();
                      (let tm' = closure_as_term cfg env tm  in
                       let start = FStar_Util.now ()  in
                       let tm_norm = nbe_eval cfg s tm'  in
                       let fin = FStar_Util.now ()  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         (let uu____74263 =
                            let uu____74265 =
                              let uu____74267 =
                                FStar_Util.time_diff start fin  in
                              FStar_Pervasives_Native.snd uu____74267  in
                            FStar_Util.string_of_int uu____74265  in
                          let uu____74274 =
                            FStar_Syntax_Print.term_to_string tm'  in
                          let uu____74276 =
                            FStar_Syntax_Print.term_to_string tm_norm  in
                          FStar_Util.print3 "NBE'd (%s ms) %s\n\tto %s\n"
                            uu____74263 uu____74274 uu____74276)
                       else ();
                       norm cfg env stack tm_norm))
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____74295 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting norm request on %s ... \n" uu____74295)
                      else ();
                      (let delta_level =
                         let uu____74303 =
                           FStar_All.pipe_right s
                             (FStar_Util.for_some
                                (fun uu___599_74310  ->
                                   match uu___599_74310 with
                                   | FStar_TypeChecker_Env.UnfoldUntil
                                       uu____74312 -> true
                                   | FStar_TypeChecker_Env.UnfoldOnly
                                       uu____74314 -> true
                                   | FStar_TypeChecker_Env.UnfoldFully
                                       uu____74318 -> true
                                   | uu____74322 -> false))
                            in
                         if uu____74303
                         then
                           [FStar_TypeChecker_Env.Unfold
                              FStar_Syntax_Syntax.delta_constant]
                         else [FStar_TypeChecker_Env.NoDelta]  in
                       let cfg'1 =
                         let uu___1893_74330 = cfg  in
                         let uu____74331 =
                           let uu___1895_74332 =
                             FStar_TypeChecker_Cfg.to_fsteps s  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.unfold_only);
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               true;
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___1895_74332.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         {
                           FStar_TypeChecker_Cfg.steps = uu____74331;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___1893_74330.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___1893_74330.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = delta_level;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___1893_74330.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong =
                             (uu___1893_74330.FStar_TypeChecker_Cfg.strong);
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___1893_74330.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___1893_74330.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let stack' =
                         let tail1 = (Cfg cfg) :: stack  in
                         if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           let uu____74340 =
                             let uu____74341 =
                               let uu____74346 = FStar_Util.now ()  in
                               (t1, uu____74346)  in
                             Debug uu____74341  in
                           uu____74340 :: tail1
                         else tail1  in
                       norm cfg'1 env stack' tm))))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____74351 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____74351
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____74362 =
                      let uu____74369 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____74369, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____74362  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____74378 = lookup_bvar env x  in
               (match uu____74378 with
                | Univ uu____74379 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                    then
                      let uu____74433 = FStar_ST.op_Bang r  in
                      (match uu____74433 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____74551  ->
                                 let uu____74552 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____74554 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____74552
                                   uu____74554);
                            (let uu____74557 = maybe_weakly_reduced t'  in
                             if uu____74557
                             then
                               match stack with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____74560 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____74637)::uu____74638 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____74649,uu____74650))::stack_rest ->
                    (match c with
                     | Univ uu____74654 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____74663 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____74693  ->
                                    let uu____74694 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____74694);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____74730  ->
                                    let uu____74731 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____74731);
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
                       (fun uu____74801  ->
                          let uu____74802 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____74802);
                     norm cfg env stack1 t1)
                | (Match uu____74805)::uu____74806 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____74821 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____74821 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____74857  -> dummy :: env1) env)
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
                                          let uu____74901 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____74901)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_74909 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_74909.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_74909.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____74910 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____74916  ->
                                 let uu____74917 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____74917);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_74932 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_74932.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_74932.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_74932.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_74932.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_74932.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_74932.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_74932.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_74932.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____74936)::uu____74937 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____74948 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____74948 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____74984  -> dummy :: env1) env)
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
                                          let uu____75028 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____75028)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_75036 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_75036.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_75036.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____75037 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____75043  ->
                                 let uu____75044 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____75044);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_75059 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_75059.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_75059.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_75059.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_75059.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_75059.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_75059.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_75059.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_75059.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____75063)::uu____75064 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____75077 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____75077 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____75113  -> dummy :: env1) env)
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
                                          let uu____75157 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____75157)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_75165 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_75165.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_75165.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____75166 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____75172  ->
                                 let uu____75173 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____75173);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_75188 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_75188.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_75188.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_75188.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_75188.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_75188.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_75188.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_75188.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_75188.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____75192)::uu____75193 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____75208 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____75208 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____75244  -> dummy :: env1) env)
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
                                          let uu____75288 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____75288)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_75296 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_75296.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_75296.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____75297 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____75303  ->
                                 let uu____75304 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____75304);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_75319 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_75319.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_75319.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_75319.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_75319.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_75319.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_75319.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_75319.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_75319.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____75323)::uu____75324 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____75339 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____75339 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____75375  -> dummy :: env1) env)
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
                                          let uu____75419 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____75419)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_75427 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_75427.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_75427.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____75428 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____75434  ->
                                 let uu____75435 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____75435);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_75450 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_75450.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_75450.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_75450.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_75450.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_75450.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_75450.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_75450.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_75450.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____75454)::uu____75455 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____75474 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____75474 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____75510  -> dummy :: env1) env)
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
                                          let uu____75554 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____75554)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_75562 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_75562.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_75562.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____75563 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____75569  ->
                                 let uu____75570 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____75570);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_75585 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_75585.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_75585.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_75585.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_75585.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_75585.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_75585.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_75585.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_75585.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____75593 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____75593 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____75629  -> dummy :: env1) env)
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
                                          let uu____75673 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____75673)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_75681 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_75681.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_75681.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____75682 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____75688  ->
                                 let uu____75689 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____75689);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_75704 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_75704.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_75704.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_75704.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_75704.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_75704.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_75704.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_75704.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_75704.FStar_TypeChecker_Cfg.reifying)
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
                      (fun uu____75748  ->
                         fun stack1  ->
                           match uu____75748 with
                           | (a,aq) ->
                               let uu____75760 =
                                 let uu____75761 =
                                   let uu____75768 =
                                     let uu____75769 =
                                       let uu____75801 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____75801, false)  in
                                     Clos uu____75769  in
                                   (uu____75768, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____75761  in
                               uu____75760 :: stack1) args)
                  in
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____75891  ->
                     let uu____75892 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____75892);
                norm cfg env stack1 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,uu____75906) when
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
                             ((let uu___2047_75951 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2047_75951.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2047_75951.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____75952 ->
                      let uu____75967 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____75967)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____75971 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____75971 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____76002 =
                          let uu____76003 =
                            let uu____76010 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___2056_76016 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2056_76016.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___2056_76016.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____76010)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____76003  in
                        mk uu____76002 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____76040 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____76040
               else
                 (let uu____76043 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____76043 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____76051 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____76077  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____76051 c1  in
                      let t2 =
                        let uu____76101 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____76101 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____76214)::uu____76215 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____76228  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____76230)::uu____76231 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____76242  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____76244,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____76245;
                                   FStar_Syntax_Syntax.vars = uu____76246;_},uu____76247,uu____76248))::uu____76249
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____76256  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____76258)::uu____76259 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____76270  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____76272 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____76275  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____76280  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____76306 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____76306
                         | FStar_Util.Inr c ->
                             let uu____76320 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____76320
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____76343 =
                               let uu____76344 =
                                 let uu____76371 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____76371, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____76344
                                in
                             mk uu____76343 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____76406 ->
                           let uu____76407 =
                             let uu____76408 =
                               let uu____76409 =
                                 let uu____76436 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____76436, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____76409
                                in
                             mk uu____76408 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____76407))))
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
                   let uu___2135_76514 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___2137_76517 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___2137_76517.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___2135_76514.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___2135_76514.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___2135_76514.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___2135_76514.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___2135_76514.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___2135_76514.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___2135_76514.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___2135_76514.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____76558 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____76558 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___2150_76578 = cfg  in
                               let uu____76579 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2150_76578.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____76579;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2150_76578.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2150_76578.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2150_76578.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___2150_76578.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2150_76578.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2150_76578.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2150_76578.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____76586 =
                                 let uu____76587 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____76587  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____76586
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___2157_76590 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___2157_76590.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2157_76590.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2157_76590.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2157_76590.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____76591 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____76591
           | FStar_Syntax_Syntax.Tm_let
               ((uu____76604,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____76605;
                               FStar_Syntax_Syntax.lbunivs = uu____76606;
                               FStar_Syntax_Syntax.lbtyp = uu____76607;
                               FStar_Syntax_Syntax.lbeff = uu____76608;
                               FStar_Syntax_Syntax.lbdef = uu____76609;
                               FStar_Syntax_Syntax.lbattrs = uu____76610;
                               FStar_Syntax_Syntax.lbpos = uu____76611;_}::uu____76612),uu____76613)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name
                   cfg.FStar_TypeChecker_Cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____76659 =
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
               if uu____76659
               then
                 let binder =
                   let uu____76663 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____76663  in
                 let env1 =
                   let uu____76673 =
                     let uu____76680 =
                       let uu____76681 =
                         let uu____76713 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____76713,
                           false)
                          in
                       Clos uu____76681  in
                     ((FStar_Pervasives_Native.Some binder), uu____76680)  in
                   uu____76673 :: env  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____76810  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                 then
                   (FStar_TypeChecker_Cfg.log cfg
                      (fun uu____76817  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____76819 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____76819))
                 else
                   (let uu____76822 =
                      let uu____76827 =
                        let uu____76828 =
                          let uu____76835 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____76835
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____76828]  in
                      FStar_Syntax_Subst.open_term uu____76827 body  in
                    match uu____76822 with
                    | (bs,body1) ->
                        (FStar_TypeChecker_Cfg.log cfg
                           (fun uu____76862  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____76871 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____76871  in
                            FStar_Util.Inl
                              (let uu___2199_76887 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2199_76887.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2199_76887.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____76890  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___2204_76893 = lb  in
                             let uu____76894 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___2204_76893.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2204_76893.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____76894;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2204_76893.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2204_76893.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____76923  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___2211_76948 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps =
                                 (uu___2211_76948.FStar_TypeChecker_Cfg.steps);
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___2211_76948.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___2211_76948.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 (uu___2211_76948.FStar_TypeChecker_Cfg.delta_level);
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___2211_76948.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong = true;
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___2211_76948.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___2211_76948.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___2211_76948.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           FStar_TypeChecker_Cfg.log cfg1
                             (fun uu____76952  ->
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
               let uu____76973 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____76973 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____77009 =
                               let uu___2227_77010 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2227_77010.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2227_77010.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____77009  in
                           let uu____77011 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____77011 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____77037 =
                                   FStar_List.map (fun uu____77053  -> dummy)
                                     lbs1
                                    in
                                 let uu____77054 =
                                   let uu____77063 =
                                     FStar_List.map
                                       (fun uu____77085  -> dummy) xs1
                                      in
                                   FStar_List.append uu____77063 env  in
                                 FStar_List.append uu____77037 uu____77054
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____77111 =
                                       let uu___2241_77112 = rc  in
                                       let uu____77113 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___2241_77112.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____77113;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___2241_77112.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____77111
                                 | uu____77122 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___2246_77128 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___2246_77128.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___2246_77128.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___2246_77128.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___2246_77128.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____77138 =
                        FStar_List.map (fun uu____77154  -> dummy) lbs2  in
                      FStar_List.append uu____77138 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____77162 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____77162 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___2255_77178 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___2255_77178.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___2255_77178.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
               ->
               let uu____77212 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____77212
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____77233 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____77311  ->
                        match uu____77311 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___2271_77436 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2271_77436.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___2271_77436.FStar_Syntax_Syntax.sort)
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
               (match uu____77233 with
                | (rec_env,memos,uu____77671) ->
                    let uu____77726 =
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
                             let uu____78038 =
                               let uu____78045 =
                                 let uu____78046 =
                                   let uu____78078 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____78078, false)
                                    in
                                 Clos uu____78046  in
                               (FStar_Pervasives_Native.None, uu____78045)
                                in
                             uu____78038 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____78185  ->
                     let uu____78186 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____78186);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____78210 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____78214::uu____78215 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____78220) ->
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
                             | uu____78251 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____78267 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____78267
                              | uu____78280 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____78286 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____78310 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____78324 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____78338 =
                        let uu____78340 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____78342 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____78340 uu____78342
                         in
                      failwith uu____78338
                    else
                      (let uu____78347 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____78347)
                | uu____78348 -> norm cfg env stack t2))

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
              let uu____78357 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____78357 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____78371  ->
                        let uu____78372 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____78372);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____78385  ->
                        let uu____78386 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____78388 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____78386 uu____78388);
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
                      | (UnivArgs (us',uu____78407))::stack1 ->
                          ((let uu____78416 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____78416
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____78424 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____78424) us'
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
                      | uu____78460 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____78463 ->
                          let uu____78466 =
                            let uu____78468 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____78468
                             in
                          failwith uu____78466
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
                  let uu___2377_78496 = cfg  in
                  let uu____78497 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____78497;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___2377_78496.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___2377_78496.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___2377_78496.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___2377_78496.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___2377_78496.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___2377_78496.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___2377_78496.FStar_TypeChecker_Cfg.reifying)
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
                     (uu____78528,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____78529;
                                    FStar_Syntax_Syntax.vars = uu____78530;_},uu____78531,uu____78532))::uu____78533
                     -> ()
                 | uu____78538 ->
                     let uu____78541 =
                       let uu____78543 = stack_to_string stack  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____78543
                        in
                     failwith uu____78541);
                (let head0 = head1  in
                 let head2 = FStar_Syntax_Util.unascribe head1  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____78552  ->
                      let uu____78553 = FStar_Syntax_Print.tag_of_term head2
                         in
                      let uu____78555 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____78553
                        uu____78555);
                 (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                  let uu____78559 =
                    let uu____78560 = FStar_Syntax_Subst.compress head3  in
                    uu____78560.FStar_Syntax_Syntax.n  in
                  match uu____78559 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let ed =
                        let uu____78581 =
                          FStar_TypeChecker_Env.norm_eff_name
                            cfg.FStar_TypeChecker_Cfg.tcenv m
                           in
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv uu____78581
                         in
                      let uu____78582 = ed.FStar_Syntax_Syntax.bind_repr  in
                      (match uu____78582 with
                       | (uu____78583,bind_repr) ->
                           (match lb.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____78593 ->
                                failwith
                                  "Cannot reify a top-level let binding"
                            | FStar_Util.Inl x ->
                                let is_return e =
                                  let uu____78604 =
                                    let uu____78605 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____78605.FStar_Syntax_Syntax.n  in
                                  match uu____78604 with
                                  | FStar_Syntax_Syntax.Tm_meta
                                      (e1,FStar_Syntax_Syntax.Meta_monadic
                                       (uu____78611,uu____78612))
                                      ->
                                      let uu____78621 =
                                        let uu____78622 =
                                          FStar_Syntax_Subst.compress e1  in
                                        uu____78622.FStar_Syntax_Syntax.n  in
                                      (match uu____78621 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                            (uu____78628,msrc,uu____78630))
                                           when
                                           FStar_Syntax_Util.is_pure_effect
                                             msrc
                                           ->
                                           let uu____78639 =
                                             FStar_Syntax_Subst.compress e2
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____78639
                                       | uu____78640 ->
                                           FStar_Pervasives_Native.None)
                                  | uu____78641 ->
                                      FStar_Pervasives_Native.None
                                   in
                                let uu____78642 =
                                  is_return lb.FStar_Syntax_Syntax.lbdef  in
                                (match uu____78642 with
                                 | FStar_Pervasives_Native.Some e ->
                                     let lb1 =
                                       let uu___2449_78647 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___2449_78647.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___2449_78647.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           (uu___2449_78647.FStar_Syntax_Syntax.lbtyp);
                                         FStar_Syntax_Syntax.lbeff =
                                           FStar_Parser_Const.effect_PURE_lid;
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___2449_78647.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___2449_78647.FStar_Syntax_Syntax.lbpos)
                                       }  in
                                     let uu____78648 = FStar_List.tl stack
                                        in
                                     let uu____78649 =
                                       let uu____78650 =
                                         let uu____78657 =
                                           let uu____78658 =
                                             let uu____78672 =
                                               FStar_Syntax_Util.mk_reify
                                                 body
                                                in
                                             ((false, [lb1]), uu____78672)
                                              in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____78658
                                            in
                                         FStar_Syntax_Syntax.mk uu____78657
                                          in
                                       uu____78650
                                         FStar_Pervasives_Native.None
                                         head3.FStar_Syntax_Syntax.pos
                                        in
                                     norm cfg env uu____78648 uu____78649
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____78691 =
                                       let uu____78693 = is_return body  in
                                       match uu____78693 with
                                       | FStar_Pervasives_Native.Some
                                           {
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_bvar y;
                                             FStar_Syntax_Syntax.pos =
                                               uu____78698;
                                             FStar_Syntax_Syntax.vars =
                                               uu____78699;_}
                                           -> FStar_Syntax_Syntax.bv_eq x y
                                       | uu____78702 -> false  in
                                     if uu____78691
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
                                          let uu____78726 =
                                            let uu____78733 =
                                              let uu____78734 =
                                                let uu____78753 =
                                                  let uu____78762 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____78762]  in
                                                (uu____78753, body1,
                                                  (FStar_Pervasives_Native.Some
                                                     body_rc))
                                                 in
                                              FStar_Syntax_Syntax.Tm_abs
                                                uu____78734
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____78733
                                             in
                                          uu____78726
                                            FStar_Pervasives_Native.None
                                            body1.FStar_Syntax_Syntax.pos
                                           in
                                        let close1 = closure_as_term cfg env
                                           in
                                        let bind_inst =
                                          let uu____78804 =
                                            let uu____78805 =
                                              FStar_Syntax_Subst.compress
                                                bind_repr
                                               in
                                            uu____78805.FStar_Syntax_Syntax.n
                                             in
                                          match uu____78804 with
                                          | FStar_Syntax_Syntax.Tm_uinst
                                              (bind1,uu____78811::uu____78812::[])
                                              ->
                                              let uu____78817 =
                                                let uu____78824 =
                                                  let uu____78825 =
                                                    let uu____78832 =
                                                      let uu____78833 =
                                                        let uu____78834 =
                                                          close1
                                                            lb.FStar_Syntax_Syntax.lbtyp
                                                           in
                                                        (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.FStar_TypeChecker_Cfg.tcenv
                                                          uu____78834
                                                         in
                                                      let uu____78835 =
                                                        let uu____78838 =
                                                          let uu____78839 =
                                                            close1 t  in
                                                          (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                            cfg.FStar_TypeChecker_Cfg.tcenv
                                                            uu____78839
                                                           in
                                                        [uu____78838]  in
                                                      uu____78833 ::
                                                        uu____78835
                                                       in
                                                    (bind1, uu____78832)  in
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                    uu____78825
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____78824
                                                 in
                                              uu____78817
                                                FStar_Pervasives_Native.None
                                                rng
                                          | uu____78845 ->
                                              failwith
                                                "NIY : Reification of indexed effects"
                                           in
                                        let maybe_range_arg =
                                          let uu____78860 =
                                            FStar_Util.for_some
                                              (FStar_Syntax_Util.attr_eq
                                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                                              ed.FStar_Syntax_Syntax.eff_attrs
                                             in
                                          if uu____78860
                                          then
                                            let uu____78873 =
                                              let uu____78882 =
                                                FStar_TypeChecker_Cfg.embed_simple
                                                  FStar_Syntax_Embeddings.e_range
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____78882
                                               in
                                            let uu____78883 =
                                              let uu____78894 =
                                                let uu____78903 =
                                                  FStar_TypeChecker_Cfg.embed_simple
                                                    FStar_Syntax_Embeddings.e_range
                                                    body2.FStar_Syntax_Syntax.pos
                                                    body2.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Syntax_Syntax.as_arg
                                                  uu____78903
                                                 in
                                              [uu____78894]  in
                                            uu____78873 :: uu____78883
                                          else []  in
                                        let reified =
                                          let uu____78941 =
                                            let uu____78948 =
                                              let uu____78949 =
                                                let uu____78966 =
                                                  let uu____78977 =
                                                    let uu____78988 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        lb.FStar_Syntax_Syntax.lbtyp
                                                       in
                                                    let uu____78997 =
                                                      let uu____79008 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          t
                                                         in
                                                      [uu____79008]  in
                                                    uu____78988 ::
                                                      uu____78997
                                                     in
                                                  let uu____79041 =
                                                    let uu____79052 =
                                                      let uu____79063 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          FStar_Syntax_Syntax.tun
                                                         in
                                                      let uu____79072 =
                                                        let uu____79083 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            head4
                                                           in
                                                        let uu____79092 =
                                                          let uu____79103 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          let uu____79112 =
                                                            let uu____79123 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                body2
                                                               in
                                                            [uu____79123]  in
                                                          uu____79103 ::
                                                            uu____79112
                                                           in
                                                        uu____79083 ::
                                                          uu____79092
                                                         in
                                                      uu____79063 ::
                                                        uu____79072
                                                       in
                                                    FStar_List.append
                                                      maybe_range_arg
                                                      uu____79052
                                                     in
                                                  FStar_List.append
                                                    uu____78977 uu____79041
                                                   in
                                                (bind_inst, uu____78966)  in
                                              FStar_Syntax_Syntax.Tm_app
                                                uu____78949
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____78948
                                             in
                                          uu____78941
                                            FStar_Pervasives_Native.None rng
                                           in
                                        FStar_TypeChecker_Cfg.log cfg
                                          (fun uu____79207  ->
                                             let uu____79208 =
                                               FStar_Syntax_Print.term_to_string
                                                 head0
                                                in
                                             let uu____79210 =
                                               FStar_Syntax_Print.term_to_string
                                                 reified
                                                in
                                             FStar_Util.print2
                                               "Reified (1) <%s> to %s\n"
                                               uu____79208 uu____79210);
                                        (let uu____79213 =
                                           FStar_List.tl stack  in
                                         norm cfg env uu____79213 reified)))))
                  | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                      ((let uu____79241 = FStar_Options.defensive ()  in
                        if uu____79241
                        then
                          let is_arg_impure uu____79256 =
                            match uu____79256 with
                            | (e,q) ->
                                let uu____79270 =
                                  let uu____79271 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____79271.FStar_Syntax_Syntax.n  in
                                (match uu____79270 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____79287 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____79287
                                 | uu____79289 -> false)
                             in
                          let uu____79291 =
                            let uu____79293 =
                              let uu____79304 =
                                FStar_Syntax_Syntax.as_arg head_app  in
                              uu____79304 :: args  in
                            FStar_Util.for_some is_arg_impure uu____79293  in
                          (if uu____79291
                           then
                             let uu____79330 =
                               let uu____79336 =
                                 let uu____79338 =
                                   FStar_Syntax_Print.term_to_string head3
                                    in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____79338
                                  in
                               (FStar_Errors.Warning_Defensive, uu____79336)
                                in
                             FStar_Errors.log_issue
                               head3.FStar_Syntax_Syntax.pos uu____79330
                           else ())
                        else ());
                       (let fallback1 uu____79351 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____79355  ->
                               let uu____79356 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____79356 "");
                          (let uu____79360 = FStar_List.tl stack  in
                           let uu____79361 = FStar_Syntax_Util.mk_reify head3
                              in
                           norm cfg env uu____79360 uu____79361)
                           in
                        let fallback2 uu____79367 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____79371  ->
                               let uu____79372 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____79372 "");
                          (let uu____79376 = FStar_List.tl stack  in
                           let uu____79377 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (head3,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               head0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env uu____79376 uu____79377)
                           in
                        let uu____79382 =
                          let uu____79383 =
                            FStar_Syntax_Util.un_uinst head_app  in
                          uu____79383.FStar_Syntax_Syntax.n  in
                        match uu____79382 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____79389 =
                              let uu____79391 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____79391  in
                            if uu____79389
                            then fallback1 ()
                            else
                              (let uu____79396 =
                                 let uu____79398 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____79398  in
                               if uu____79396
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____79415 =
                                      let uu____79420 =
                                        FStar_Syntax_Util.mk_reify head_app
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____79420 args
                                       in
                                    uu____79415 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____79423 = FStar_List.tl stack  in
                                  norm cfg env uu____79423 t1))
                        | uu____79424 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____79426) ->
                      do_reify_monadic fallback cfg env stack e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____79450 = closure_as_term cfg env t'  in
                        reify_lift cfg e msrc mtgt uu____79450  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____79454  ->
                            let uu____79455 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____79455);
                       (let uu____79458 = FStar_List.tl stack  in
                        norm cfg env uu____79458 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                      let branches1 =
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun uu____79579  ->
                                match uu____79579 with
                                | (pat,wopt,tm) ->
                                    let uu____79627 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____79627)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                          head3.FStar_Syntax_Syntax.pos
                         in
                      let uu____79659 = FStar_List.tl stack  in
                      norm cfg env uu____79659 tm
                  | uu____79660 -> fallback ()))

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
              (fun uu____79674  ->
                 let uu____79675 = FStar_Ident.string_of_lid msrc  in
                 let uu____79677 = FStar_Ident.string_of_lid mtgt  in
                 let uu____79679 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____79675
                   uu____79677 uu____79679);
            (let uu____79682 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____79682
             then
               let ed =
                 let uu____79686 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____79686  in
               let uu____79687 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____79687 with
               | (uu____79688,return_repr) ->
                   let return_inst =
                     let uu____79701 =
                       let uu____79702 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____79702.FStar_Syntax_Syntax.n  in
                     match uu____79701 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____79708::[]) ->
                         let uu____79713 =
                           let uu____79720 =
                             let uu____79721 =
                               let uu____79728 =
                                 let uu____79729 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____79729]  in
                               (return_tm, uu____79728)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____79721  in
                           FStar_Syntax_Syntax.mk uu____79720  in
                         uu____79713 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____79735 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____79739 =
                     let uu____79746 =
                       let uu____79747 =
                         let uu____79764 =
                           let uu____79775 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____79784 =
                             let uu____79795 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____79795]  in
                           uu____79775 :: uu____79784  in
                         (return_inst, uu____79764)  in
                       FStar_Syntax_Syntax.Tm_app uu____79747  in
                     FStar_Syntax_Syntax.mk uu____79746  in
                   uu____79739 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____79845 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____79845 with
                | FStar_Pervasives_Native.None  ->
                    let uu____79848 =
                      let uu____79850 = FStar_Ident.text_of_lid msrc  in
                      let uu____79852 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____79850 uu____79852
                       in
                    failwith uu____79848
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____79855;
                      FStar_TypeChecker_Env.mtarget = uu____79856;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____79857;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____79879 =
                      let uu____79881 = FStar_Ident.text_of_lid msrc  in
                      let uu____79883 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____79881 uu____79883
                       in
                    failwith uu____79879
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____79886;
                      FStar_TypeChecker_Env.mtarget = uu____79887;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____79888;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____79923 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____79924 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____79923 t FStar_Syntax_Syntax.tun uu____79924))

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
                (fun uu____79994  ->
                   match uu____79994 with
                   | (a,imp) ->
                       let uu____80013 = norm cfg env [] a  in
                       (uu____80013, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____80023  ->
             let uu____80024 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____80026 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____80024 uu____80026);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____80052 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _80055  -> FStar_Pervasives_Native.Some _80055)
                     uu____80052
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2599_80056 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2599_80056.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2599_80056.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____80078 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _80081  -> FStar_Pervasives_Native.Some _80081)
                     uu____80078
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2610_80082 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2610_80082.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2610_80082.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____80127  ->
                      match uu____80127 with
                      | (a,i) ->
                          let uu____80147 = norm cfg env [] a  in
                          (uu____80147, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___600_80169  ->
                       match uu___600_80169 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____80173 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____80173
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___2627_80181 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2629_80184 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2629_80184.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2627_80181.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2627_80181.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun b  ->
        let uu____80188 = b  in
        match uu____80188 with
        | (x,imp) ->
            let x1 =
              let uu___2637_80196 = x  in
              let uu____80197 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2637_80196.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2637_80196.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____80197
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____80208 =
                    let uu____80209 = closure_as_term cfg env t  in
                    FStar_Syntax_Syntax.Meta uu____80209  in
                  FStar_Pervasives_Native.Some uu____80208
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____80220 =
          FStar_List.fold_left
            (fun uu____80254  ->
               fun b  ->
                 match uu____80254 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____80220 with | (nbs,uu____80334) -> FStar_List.rev nbs

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
            let uu____80366 =
              let uu___2662_80367 = rc  in
              let uu____80368 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2662_80367.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____80368;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2662_80367.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____80366
        | uu____80377 -> lopt

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
            (let uu____80387 = FStar_Syntax_Print.term_to_string tm  in
             let uu____80389 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____80387 uu____80389)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___601_80401  ->
      match uu___601_80401 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____80414 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____80414 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____80418 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____80418)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____80426 = norm_cb cfg  in
            reduce_primops uu____80426 cfg env tm  in
          let uu____80433 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____80433
          then tm1
          else
            (let w t =
               let uu___2690_80452 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2690_80452.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2690_80452.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____80464 =
                 let uu____80465 = FStar_Syntax_Util.unmeta t  in
                 uu____80465.FStar_Syntax_Syntax.n  in
               match uu____80464 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____80477 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____80541)::args1,(bv,uu____80544)::bs1) ->
                   let uu____80598 =
                     let uu____80599 = FStar_Syntax_Subst.compress t  in
                     uu____80599.FStar_Syntax_Syntax.n  in
                   (match uu____80598 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____80604 -> false)
               | ([],[]) -> true
               | (uu____80635,uu____80636) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____80687 = FStar_Syntax_Print.term_to_string t  in
                  let uu____80689 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____80687
                    uu____80689)
               else ();
               (let uu____80694 = FStar_Syntax_Util.head_and_args' t  in
                match uu____80694 with
                | (hd1,args) ->
                    let uu____80733 =
                      let uu____80734 = FStar_Syntax_Subst.compress hd1  in
                      uu____80734.FStar_Syntax_Syntax.n  in
                    (match uu____80733 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____80742 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____80744 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____80746 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____80742 uu____80744 uu____80746)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____80751 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____80769 = FStar_Syntax_Print.term_to_string t  in
                  let uu____80771 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____80769
                    uu____80771)
               else ();
               (let uu____80776 = FStar_Syntax_Util.is_squash t  in
                match uu____80776 with
                | FStar_Pervasives_Native.Some (uu____80787,t') ->
                    is_applied bs t'
                | uu____80799 ->
                    let uu____80808 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____80808 with
                     | FStar_Pervasives_Native.Some (uu____80819,t') ->
                         is_applied bs t'
                     | uu____80831 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____80855 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____80855 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____80862)::(q,uu____80864)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____80907 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____80909 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____80907 uu____80909)
                    else ();
                    (let uu____80914 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____80914 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____80919 =
                           let uu____80920 = FStar_Syntax_Subst.compress p
                              in
                           uu____80920.FStar_Syntax_Syntax.n  in
                         (match uu____80919 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____80931 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____80931))
                          | uu____80934 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____80937)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____80962 =
                           let uu____80963 = FStar_Syntax_Subst.compress p1
                              in
                           uu____80963.FStar_Syntax_Syntax.n  in
                         (match uu____80962 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____80974 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____80974))
                          | uu____80977 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____80981 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____80981 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____80986 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____80986 with
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
                                     let uu____81000 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____81000))
                               | uu____81003 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____81008)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____81033 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____81033 with
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
                                     let uu____81047 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____81047))
                               | uu____81050 -> FStar_Pervasives_Native.None)
                          | uu____81053 -> FStar_Pervasives_Native.None)
                     | uu____81056 -> FStar_Pervasives_Native.None))
               | uu____81059 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____81072 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____81072 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____81078)::[],uu____81079,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____81099 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____81101 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____81099
                         uu____81101)
                    else ();
                    is_quantified_const bv phi')
               | uu____81106 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____81121 =
                 let uu____81122 = FStar_Syntax_Subst.compress phi  in
                 uu____81122.FStar_Syntax_Syntax.n  in
               match uu____81121 with
               | FStar_Syntax_Syntax.Tm_match (uu____81128,br::brs) ->
                   let uu____81195 = br  in
                   (match uu____81195 with
                    | (uu____81213,uu____81214,e) ->
                        let r =
                          let uu____81236 = simp_t e  in
                          match uu____81236 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____81248 =
                                FStar_List.for_all
                                  (fun uu____81267  ->
                                     match uu____81267 with
                                     | (uu____81281,uu____81282,e') ->
                                         let uu____81296 = simp_t e'  in
                                         uu____81296 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____81248
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____81312 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____81322 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____81322
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____81360 =
                 match uu____81360 with
                 | (t1,q) ->
                     let uu____81381 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____81381 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____81413 -> (t1, q))
                  in
               let uu____81426 = FStar_Syntax_Util.head_and_args t  in
               match uu____81426 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____81506 =
                 let uu____81507 = FStar_Syntax_Util.unmeta ty  in
                 uu____81507.FStar_Syntax_Syntax.n  in
               match uu____81506 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____81512) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____81517,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____81541 -> false  in
             let simplify1 arg =
               let uu____81574 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____81574, arg)  in
             let uu____81589 = is_forall_const tm1  in
             match uu____81589 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____81595 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____81597 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____81595
                       uu____81597)
                  else ();
                  (let uu____81602 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____81602))
             | FStar_Pervasives_Native.None  ->
                 let uu____81603 =
                   let uu____81604 = FStar_Syntax_Subst.compress tm1  in
                   uu____81604.FStar_Syntax_Syntax.n  in
                 (match uu____81603 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____81608;
                              FStar_Syntax_Syntax.vars = uu____81609;_},uu____81610);
                         FStar_Syntax_Syntax.pos = uu____81611;
                         FStar_Syntax_Syntax.vars = uu____81612;_},args)
                      ->
                      let uu____81642 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____81642
                      then
                        let uu____81645 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____81645 with
                         | (FStar_Pervasives_Native.Some (true ),uu____81703)::
                             (uu____81704,(arg,uu____81706))::[] ->
                             maybe_auto_squash arg
                         | (uu____81779,(arg,uu____81781))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____81782)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____81855)::uu____81856::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____81926::(FStar_Pervasives_Native.Some (false
                                         ),uu____81927)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____81997 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____82015 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____82015
                         then
                           let uu____82018 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____82018 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____82076)::uu____82077::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____82147::(FStar_Pervasives_Native.Some (true
                                           ),uu____82148)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____82218)::(uu____82219,(arg,uu____82221))::[]
                               -> maybe_auto_squash arg
                           | (uu____82294,(arg,uu____82296))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____82297)::[]
                               -> maybe_auto_squash arg
                           | uu____82370 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____82388 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____82388
                            then
                              let uu____82391 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____82391 with
                              | uu____82449::(FStar_Pervasives_Native.Some
                                              (true ),uu____82450)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____82520)::uu____82521::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____82591)::(uu____82592,(arg,uu____82594))::[]
                                  -> maybe_auto_squash arg
                              | (uu____82667,(p,uu____82669))::(uu____82670,
                                                                (q,uu____82672))::[]
                                  ->
                                  let uu____82744 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____82744
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____82749 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____82767 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____82767
                               then
                                 let uu____82770 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____82770 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____82828)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____82829)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____82903)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____82904)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____82978)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____82979)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____83053)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____83054)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____83128,(arg,uu____83130))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____83131)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____83204)::(uu____83205,(arg,uu____83207))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____83280,(arg,uu____83282))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____83283)::[]
                                     ->
                                     let uu____83356 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____83356
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____83357)::(uu____83358,(arg,uu____83360))::[]
                                     ->
                                     let uu____83433 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____83433
                                 | (uu____83434,(p,uu____83436))::(uu____83437,
                                                                   (q,uu____83439))::[]
                                     ->
                                     let uu____83511 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____83511
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____83516 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____83534 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____83534
                                  then
                                    let uu____83537 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____83537 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____83595)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____83639)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____83683 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____83701 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____83701
                                     then
                                       match args with
                                       | (t,uu____83705)::[] ->
                                           let uu____83730 =
                                             let uu____83731 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____83731.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____83730 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____83734::[],body,uu____83736)
                                                ->
                                                let uu____83771 = simp_t body
                                                   in
                                                (match uu____83771 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____83777 -> tm1)
                                            | uu____83781 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____83783))::(t,uu____83785)::[]
                                           ->
                                           let uu____83825 =
                                             let uu____83826 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____83826.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____83825 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____83829::[],body,uu____83831)
                                                ->
                                                let uu____83866 = simp_t body
                                                   in
                                                (match uu____83866 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____83874 -> tm1)
                                            | uu____83878 -> tm1)
                                       | uu____83879 -> tm1
                                     else
                                       (let uu____83892 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____83892
                                        then
                                          match args with
                                          | (t,uu____83896)::[] ->
                                              let uu____83921 =
                                                let uu____83922 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____83922.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____83921 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____83925::[],body,uu____83927)
                                                   ->
                                                   let uu____83962 =
                                                     simp_t body  in
                                                   (match uu____83962 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____83968 -> tm1)
                                               | uu____83972 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____83974))::(t,uu____83976)::[]
                                              ->
                                              let uu____84016 =
                                                let uu____84017 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____84017.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____84016 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____84020::[],body,uu____84022)
                                                   ->
                                                   let uu____84057 =
                                                     simp_t body  in
                                                   (match uu____84057 with
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
                                                    | uu____84065 -> tm1)
                                               | uu____84069 -> tm1)
                                          | uu____84070 -> tm1
                                        else
                                          (let uu____84083 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____84083
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____84086;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____84087;_},uu____84088)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____84114;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____84115;_},uu____84116)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____84142 -> tm1
                                           else
                                             (let uu____84155 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____84155
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____84169 =
                                                    let uu____84170 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____84170.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____84169 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____84181 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     (Prims.parse_int "1")
                                                 then
                                                   let t =
                                                     let uu____84195 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____84195
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____84234 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____84234
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____84240 =
                                                         let uu____84241 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____84241.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____84240 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____84244 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____84252 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____84252
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____84261
                                                                  =
                                                                  let uu____84262
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____84262.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____84261
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____84268)
                                                                    -> hd1
                                                                | uu____84293
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____84297
                                                                =
                                                                let uu____84308
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____84308]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____84297)
                                                       | uu____84341 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____84346 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____84346 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____84366 ->
                                                     let uu____84375 =
                                                       let uu____84382 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____84382 cfg env
                                                        in
                                                     uu____84375 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____84390;
                         FStar_Syntax_Syntax.vars = uu____84391;_},args)
                      ->
                      let uu____84417 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____84417
                      then
                        let uu____84420 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____84420 with
                         | (FStar_Pervasives_Native.Some (true ),uu____84478)::
                             (uu____84479,(arg,uu____84481))::[] ->
                             maybe_auto_squash arg
                         | (uu____84554,(arg,uu____84556))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____84557)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____84630)::uu____84631::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____84701::(FStar_Pervasives_Native.Some (false
                                         ),uu____84702)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____84772 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____84790 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____84790
                         then
                           let uu____84793 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____84793 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____84851)::uu____84852::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____84922::(FStar_Pervasives_Native.Some (true
                                           ),uu____84923)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____84993)::(uu____84994,(arg,uu____84996))::[]
                               -> maybe_auto_squash arg
                           | (uu____85069,(arg,uu____85071))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____85072)::[]
                               -> maybe_auto_squash arg
                           | uu____85145 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____85163 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____85163
                            then
                              let uu____85166 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____85166 with
                              | uu____85224::(FStar_Pervasives_Native.Some
                                              (true ),uu____85225)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____85295)::uu____85296::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____85366)::(uu____85367,(arg,uu____85369))::[]
                                  -> maybe_auto_squash arg
                              | (uu____85442,(p,uu____85444))::(uu____85445,
                                                                (q,uu____85447))::[]
                                  ->
                                  let uu____85519 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____85519
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____85524 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____85542 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____85542
                               then
                                 let uu____85545 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____85545 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____85603)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____85604)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____85678)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____85679)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____85753)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____85754)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____85828)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____85829)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____85903,(arg,uu____85905))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____85906)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____85979)::(uu____85980,(arg,uu____85982))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____86055,(arg,uu____86057))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____86058)::[]
                                     ->
                                     let uu____86131 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____86131
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____86132)::(uu____86133,(arg,uu____86135))::[]
                                     ->
                                     let uu____86208 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____86208
                                 | (uu____86209,(p,uu____86211))::(uu____86212,
                                                                   (q,uu____86214))::[]
                                     ->
                                     let uu____86286 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____86286
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____86291 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____86309 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____86309
                                  then
                                    let uu____86312 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____86312 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____86370)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____86414)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____86458 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____86476 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____86476
                                     then
                                       match args with
                                       | (t,uu____86480)::[] ->
                                           let uu____86505 =
                                             let uu____86506 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____86506.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____86505 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____86509::[],body,uu____86511)
                                                ->
                                                let uu____86546 = simp_t body
                                                   in
                                                (match uu____86546 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____86552 -> tm1)
                                            | uu____86556 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____86558))::(t,uu____86560)::[]
                                           ->
                                           let uu____86600 =
                                             let uu____86601 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____86601.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____86600 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____86604::[],body,uu____86606)
                                                ->
                                                let uu____86641 = simp_t body
                                                   in
                                                (match uu____86641 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____86649 -> tm1)
                                            | uu____86653 -> tm1)
                                       | uu____86654 -> tm1
                                     else
                                       (let uu____86667 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____86667
                                        then
                                          match args with
                                          | (t,uu____86671)::[] ->
                                              let uu____86696 =
                                                let uu____86697 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____86697.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____86696 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____86700::[],body,uu____86702)
                                                   ->
                                                   let uu____86737 =
                                                     simp_t body  in
                                                   (match uu____86737 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____86743 -> tm1)
                                               | uu____86747 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____86749))::(t,uu____86751)::[]
                                              ->
                                              let uu____86791 =
                                                let uu____86792 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____86792.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____86791 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____86795::[],body,uu____86797)
                                                   ->
                                                   let uu____86832 =
                                                     simp_t body  in
                                                   (match uu____86832 with
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
                                                    | uu____86840 -> tm1)
                                               | uu____86844 -> tm1)
                                          | uu____86845 -> tm1
                                        else
                                          (let uu____86858 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____86858
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____86861;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____86862;_},uu____86863)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____86889;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____86890;_},uu____86891)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____86917 -> tm1
                                           else
                                             (let uu____86930 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____86930
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____86944 =
                                                    let uu____86945 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____86945.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____86944 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____86956 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     (Prims.parse_int "1")
                                                 then
                                                   let t =
                                                     let uu____86970 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____86970
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____87005 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____87005
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____87011 =
                                                         let uu____87012 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____87012.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____87011 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____87015 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____87023 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____87023
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____87032
                                                                  =
                                                                  let uu____87033
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____87033.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____87032
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____87039)
                                                                    -> hd1
                                                                | uu____87064
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____87068
                                                                =
                                                                let uu____87079
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____87079]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____87068)
                                                       | uu____87112 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____87117 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____87117 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____87137 ->
                                                     let uu____87146 =
                                                       let uu____87153 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____87153 cfg env
                                                        in
                                                     uu____87146 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____87166 = simp_t t  in
                      (match uu____87166 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____87175 ->
                      let uu____87198 = is_const_match tm1  in
                      (match uu____87198 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____87207 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____87217  ->
               (let uu____87219 = FStar_Syntax_Print.tag_of_term t  in
                let uu____87221 = FStar_Syntax_Print.term_to_string t  in
                let uu____87223 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____87231 =
                  let uu____87233 =
                    let uu____87236 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____87236
                     in
                  stack_to_string uu____87233  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____87219 uu____87221 uu____87223 uu____87231);
               (let uu____87261 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____87261
                then
                  let uu____87265 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____87265 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____87272 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____87274 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____87276 =
                          let uu____87278 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____87278
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____87272
                          uu____87274 uu____87276);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____87300 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack with
                | (Arg uu____87308)::uu____87309 -> true
                | uu____87319 -> false)
              in
           if uu____87300
           then
             let uu____87322 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____87322 (norm cfg env stack)
           else
             (let t1 = maybe_simplify cfg env stack t  in
              match stack with
              | [] -> t1
              | (Debug (tm,time_then))::stack1 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now ()  in
                      let uu____87336 =
                        let uu____87338 =
                          let uu____87340 =
                            FStar_Util.time_diff time_then time_now  in
                          FStar_Pervasives_Native.snd uu____87340  in
                        FStar_Util.string_of_int uu____87338  in
                      let uu____87347 = FStar_Syntax_Print.term_to_string tm
                         in
                      let uu____87349 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print3
                        "Normalized term (%s ms) %s\n\tto term %s\n"
                        uu____87336 uu____87347 uu____87349)
                   else ();
                   rebuild cfg env stack1 t1)
              | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
              | (Meta (uu____87358,m,r))::stack1 ->
                  let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
                  rebuild cfg env stack1 t2
              | (MemoLazy r)::stack1 ->
                  (set_memo cfg r (env, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu____87409  ->
                        let uu____87410 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 "\tSet memo %s\n" uu____87410);
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
                  let uu____87453 =
                    let uu___3319_87454 = FStar_Syntax_Util.abs bs1 t1 lopt1
                       in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___3319_87454.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___3319_87454.FStar_Syntax_Syntax.vars)
                    }  in
                  rebuild cfg env stack1 uu____87453
              | (Arg (Univ uu____87457,uu____87458,uu____87459))::uu____87460
                  -> failwith "Impossible"
              | (Arg (Dummy ,uu____87464,uu____87465))::uu____87466 ->
                  failwith "Impossible"
              | (UnivArgs (us,r))::stack1 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                  rebuild cfg env stack1 t2
              | (Arg
                  (Clos (env_arg,tm,uu____87482,uu____87483),aq,r))::stack1
                  when
                  let uu____87535 = head_of t1  in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____87535 ->
                  let t2 =
                    let uu____87539 =
                      let uu____87544 =
                        let uu____87545 = closure_as_term cfg env_arg tm  in
                        (uu____87545, aq)  in
                      FStar_Syntax_Syntax.extend_app t1 uu____87544  in
                    uu____87539 FStar_Pervasives_Native.None r  in
                  rebuild cfg env stack1 t2
              | (Arg (Clos (env_arg,tm,m,uu____87557),aq,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____87612  ->
                        let uu____87613 =
                          FStar_Syntax_Print.term_to_string tm  in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____87613);
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
                     (let uu____87633 = FStar_ST.op_Bang m  in
                      match uu____87633 with
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
                      | FStar_Pervasives_Native.Some (uu____87776,a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq)
                              FStar_Pervasives_Native.None r
                             in
                          rebuild cfg env_arg stack1 t2))
              | (App (env1,head1,aq,r))::stack' when should_reify cfg stack
                  ->
                  let t0 = t1  in
                  let fallback msg uu____87832 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____87837  ->
                         let uu____87838 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____87838);
                    (let t2 =
                       FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env1 stack' t2)
                     in
                  let uu____87848 =
                    let uu____87849 = FStar_Syntax_Subst.compress t1  in
                    uu____87849.FStar_Syntax_Syntax.n  in
                  (match uu____87848 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env1 stack t2 m
                         ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc,mtgt,ty))
                       ->
                       let lifted =
                         let uu____87877 = closure_as_term cfg env1 ty  in
                         reify_lift cfg t2 msrc mtgt uu____87877  in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____87881  ->
                             let uu____87882 =
                               FStar_Syntax_Print.term_to_string lifted  in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____87882);
                        (let uu____87885 = FStar_List.tl stack  in
                         norm cfg env1 uu____87885 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu____87886);
                          FStar_Syntax_Syntax.pos = uu____87887;
                          FStar_Syntax_Syntax.vars = uu____87888;_},(e,uu____87890)::[])
                       -> norm cfg env1 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____87929 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____87946 = FStar_Syntax_Util.head_and_args t1
                          in
                       (match uu____87946 with
                        | (hd1,args) ->
                            let uu____87989 =
                              let uu____87990 =
                                FStar_Syntax_Util.un_uinst hd1  in
                              uu____87990.FStar_Syntax_Syntax.n  in
                            (match uu____87989 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____87994 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv
                                    in
                                 (match uu____87994 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____87997;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____87998;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____87999;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n1;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____88001;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____88002;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____88003;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____88004;_}
                                      when (FStar_List.length args) = n1 ->
                                      norm cfg env1 stack' t1
                                  | uu____88041 -> fallback " (3)" ())
                             | uu____88045 -> fallback " (4)" ()))
                   | uu____88047 -> fallback " (2)" ())
              | (App (env1,head1,aq,r))::stack1 ->
                  let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack1 t2
              | (Match (env',branches,cfg1,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____88073  ->
                        let uu____88074 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____88074);
                   (let scrutinee_env = env  in
                    let env1 = env'  in
                    let scrutinee = t1  in
                    let norm_and_rebuild_match uu____88085 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____88090  ->
                           let uu____88091 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           let uu____88093 =
                             let uu____88095 =
                               FStar_All.pipe_right branches
                                 (FStar_List.map
                                    (fun uu____88125  ->
                                       match uu____88125 with
                                       | (p,uu____88136,uu____88137) ->
                                           FStar_Syntax_Print.pat_to_string p))
                                in
                             FStar_All.pipe_right uu____88095
                               (FStar_String.concat "\n\t")
                              in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu____88091 uu____88093);
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
                                (fun uu___602_88159  ->
                                   match uu___602_88159 with
                                   | FStar_TypeChecker_Env.InliningDelta  ->
                                       true
                                   | FStar_TypeChecker_Env.Eager_unfolding_only
                                        -> true
                                   | uu____88163 -> false))
                            in
                         let steps =
                           let uu___3487_88166 =
                             cfg1.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___3487_88166.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___3487_88166.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta = false;
                             FStar_TypeChecker_Cfg.weak =
                               (uu___3487_88166.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___3487_88166.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___3487_88166.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___3487_88166.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_only =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___3487_88166.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_tac = false;
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___3487_88166.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___3487_88166.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___3487_88166.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___3487_88166.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___3487_88166.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___3487_88166.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___3487_88166.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___3487_88166.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___3487_88166.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___3487_88166.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___3487_88166.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___3487_88166.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___3487_88166.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___3487_88166.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         let uu___3490_88173 = cfg1  in
                         {
                           FStar_TypeChecker_Cfg.steps = steps;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___3490_88173.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___3490_88173.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = new_delta;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___3490_88173.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong = true;
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___3490_88173.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets =
                             (uu___3490_88173.FStar_TypeChecker_Cfg.normalize_pure_lets);
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___3490_88173.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let norm_or_whnf env2 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env2 t2
                         else norm cfg_exclude_zeta env2 [] t2  in
                       let rec norm_pat env2 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu____88248 ->
                             (p, env2)
                         | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                             let uu____88279 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____88368  ->
                                       fun uu____88369  ->
                                         match (uu____88368, uu____88369)
                                         with
                                         | ((pats1,env3),(p1,b)) ->
                                             let uu____88519 =
                                               norm_pat env3 p1  in
                                             (match uu____88519 with
                                              | (p2,env4) ->
                                                  (((p2, b) :: pats1), env4)))
                                    ([], env2))
                                in
                             (match uu____88279 with
                              | (pats1,env3) ->
                                  ((let uu___3518_88689 = p  in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___3518_88689.FStar_Syntax_Syntax.p)
                                    }), env3))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___3522_88710 = x  in
                               let uu____88711 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3522_88710.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3522_88710.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____88711
                               }  in
                             ((let uu___3525_88725 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3525_88725.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___3529_88736 = x  in
                               let uu____88737 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3529_88736.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3529_88736.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____88737
                               }  in
                             ((let uu___3532_88751 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3532_88751.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                             let x1 =
                               let uu___3538_88767 = x  in
                               let uu____88768 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3538_88767.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3538_88767.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____88768
                               }  in
                             let t3 = norm_or_whnf env2 t2  in
                             ((let uu___3542_88783 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___3542_88783.FStar_Syntax_Syntax.p)
                               }), env2)
                          in
                       let branches1 =
                         match env1 with
                         | [] when whnf -> branches
                         | uu____88827 ->
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun branch1  ->
                                     let uu____88857 =
                                       FStar_Syntax_Subst.open_branch branch1
                                        in
                                     match uu____88857 with
                                     | (p,wopt,e) ->
                                         let uu____88877 = norm_pat env1 p
                                            in
                                         (match uu____88877 with
                                          | (p1,env2) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu____88932 =
                                                      norm_or_whnf env2 w  in
                                                    FStar_Pervasives_Native.Some
                                                      uu____88932
                                                 in
                                              let e1 = norm_or_whnf env2 e
                                                 in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1))))
                          in
                       let scrutinee1 =
                         let uu____88949 =
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
                         if uu____88949
                         then
                           norm
                             (let uu___3561_88956 = cfg1  in
                              {
                                FStar_TypeChecker_Cfg.steps =
                                  (let uu___3563_88959 =
                                     cfg1.FStar_TypeChecker_Cfg.steps  in
                                   {
                                     FStar_TypeChecker_Cfg.beta =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.beta);
                                     FStar_TypeChecker_Cfg.iota =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.iota);
                                     FStar_TypeChecker_Cfg.zeta =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.zeta);
                                     FStar_TypeChecker_Cfg.weak =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.weak);
                                     FStar_TypeChecker_Cfg.hnf =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.hnf);
                                     FStar_TypeChecker_Cfg.primops =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.primops);
                                     FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                       =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                     FStar_TypeChecker_Cfg.unfold_until =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.unfold_until);
                                     FStar_TypeChecker_Cfg.unfold_only =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.unfold_only);
                                     FStar_TypeChecker_Cfg.unfold_fully =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.unfold_fully);
                                     FStar_TypeChecker_Cfg.unfold_attr =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.unfold_attr);
                                     FStar_TypeChecker_Cfg.unfold_tac =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.unfold_tac);
                                     FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                       =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                     FStar_TypeChecker_Cfg.simplify =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.simplify);
                                     FStar_TypeChecker_Cfg.erase_universes =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.erase_universes);
                                     FStar_TypeChecker_Cfg.allow_unbound_universes
                                       =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                     FStar_TypeChecker_Cfg.reify_ =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.reify_);
                                     FStar_TypeChecker_Cfg.compress_uvars =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.compress_uvars);
                                     FStar_TypeChecker_Cfg.no_full_norm =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.no_full_norm);
                                     FStar_TypeChecker_Cfg.check_no_uvars =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.check_no_uvars);
                                     FStar_TypeChecker_Cfg.unmeta =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.unmeta);
                                     FStar_TypeChecker_Cfg.unascribe =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.unascribe);
                                     FStar_TypeChecker_Cfg.in_full_norm_request
                                       =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.in_full_norm_request);
                                     FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                       = false;
                                     FStar_TypeChecker_Cfg.nbe_step =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.nbe_step);
                                     FStar_TypeChecker_Cfg.for_extraction =
                                       (uu___3563_88959.FStar_TypeChecker_Cfg.for_extraction)
                                   });
                                FStar_TypeChecker_Cfg.tcenv =
                                  (uu___3561_88956.FStar_TypeChecker_Cfg.tcenv);
                                FStar_TypeChecker_Cfg.debug =
                                  (uu___3561_88956.FStar_TypeChecker_Cfg.debug);
                                FStar_TypeChecker_Cfg.delta_level =
                                  (uu___3561_88956.FStar_TypeChecker_Cfg.delta_level);
                                FStar_TypeChecker_Cfg.primitive_steps =
                                  (uu___3561_88956.FStar_TypeChecker_Cfg.primitive_steps);
                                FStar_TypeChecker_Cfg.strong =
                                  (uu___3561_88956.FStar_TypeChecker_Cfg.strong);
                                FStar_TypeChecker_Cfg.memoize_lazy =
                                  (uu___3561_88956.FStar_TypeChecker_Cfg.memoize_lazy);
                                FStar_TypeChecker_Cfg.normalize_pure_lets =
                                  (uu___3561_88956.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                FStar_TypeChecker_Cfg.reifying =
                                  (uu___3561_88956.FStar_TypeChecker_Cfg.reifying)
                              }) scrutinee_env [] scrutinee
                         else scrutinee  in
                       let uu____88963 =
                         mk
                           (FStar_Syntax_Syntax.Tm_match
                              (scrutinee1, branches1)) r
                          in
                       rebuild cfg1 env1 stack1 uu____88963)
                       in
                    let rec is_cons head1 =
                      let uu____88989 =
                        let uu____88990 = FStar_Syntax_Subst.compress head1
                           in
                        uu____88990.FStar_Syntax_Syntax.n  in
                      match uu____88989 with
                      | FStar_Syntax_Syntax.Tm_uinst (h,uu____88995) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____89000 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____89002;
                            FStar_Syntax_Syntax.fv_delta = uu____89003;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor );_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____89005;
                            FStar_Syntax_Syntax.fv_delta = uu____89006;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____89007);_}
                          -> true
                      | uu____89015 -> false  in
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
                      let uu____89184 =
                        FStar_Syntax_Util.head_and_args scrutinee2  in
                      match uu____89184 with
                      | (head1,args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu____89281 ->
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
                                | uu____89323 ->
                                    let uu____89324 =
                                      let uu____89326 = is_cons head1  in
                                      Prims.op_Negation uu____89326  in
                                    FStar_Util.Inr uu____89324)
                           | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                               let uu____89355 =
                                 let uu____89356 =
                                   FStar_Syntax_Util.un_uinst head1  in
                                 uu____89356.FStar_Syntax_Syntax.n  in
                               (match uu____89355 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____89375 ->
                                    let uu____89376 =
                                      let uu____89378 = is_cons head1  in
                                      Prims.op_Negation uu____89378  in
                                    FStar_Util.Inr uu____89376))
                    
                    and matches_args out a p =
                      match (a, p) with
                      | ([],[]) -> FStar_Util.Inl out
                      | ((t2,uu____89469)::rest_a,(p1,uu____89472)::rest_p)
                          ->
                          let uu____89531 = matches_pat t2 p1  in
                          (match uu____89531 with
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu____89584 -> FStar_Util.Inr false
                     in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1,wopt,b)::rest ->
                          let uu____89707 = matches_pat scrutinee1 p1  in
                          (match uu____89707 with
                           | FStar_Util.Inr (false ) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true ) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu____89753  ->
                                     let uu____89754 =
                                       FStar_Syntax_Print.pat_to_string p1
                                        in
                                     let uu____89756 =
                                       let uu____89758 =
                                         FStar_List.map
                                           (fun uu____89770  ->
                                              match uu____89770 with
                                              | (uu____89776,t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s
                                          in
                                       FStar_All.pipe_right uu____89758
                                         (FStar_String.concat "; ")
                                        in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu____89754 uu____89756);
                                (let env0 = env1  in
                                 let env2 =
                                   FStar_List.fold_left
                                     (fun env2  ->
                                        fun uu____89812  ->
                                          match uu____89812 with
                                          | (bv,t2) ->
                                              let uu____89835 =
                                                let uu____89842 =
                                                  let uu____89845 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____89845
                                                   in
                                                let uu____89846 =
                                                  let uu____89847 =
                                                    let uu____89879 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2))
                                                       in
                                                    ([], t2, uu____89879,
                                                      false)
                                                     in
                                                  Clos uu____89847  in
                                                (uu____89842, uu____89846)
                                                 in
                                              uu____89835 :: env2) env1 s
                                    in
                                 let uu____89994 =
                                   guard_when_clause wopt b rest  in
                                 norm cfg1 env2 stack1 uu____89994)))
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
            (fun uu____90027  ->
               let uu____90028 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____90028);
          (let uu____90031 = is_nbe_request s  in
           if uu____90031
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____90037  ->
                   let uu____90038 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____90038);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____90044  ->
                   let uu____90045 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____90045);
              (let uu____90048 =
                 FStar_Util.record_time (fun uu____90055  -> nbe_eval c s t)
                  in
               match uu____90048 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____90064  ->
                         let uu____90065 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____90067 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____90065 uu____90067);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____90075  ->
                   let uu____90076 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____90076);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____90082  ->
                   let uu____90083 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____90083);
              (let uu____90086 =
                 FStar_Util.record_time (fun uu____90093  -> norm c [] [] t)
                  in
               match uu____90086 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____90108  ->
                         let uu____90109 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____90111 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____90109 uu____90111);
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
        let uu____90146 = FStar_TypeChecker_Cfg.config s e  in
        norm_comp uu____90146 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____90164 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____90164 [] u
  
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
        let uu____90190 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____90190  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____90197 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___3719_90216 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3719_90216.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3719_90216.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name
              cfg.FStar_TypeChecker_Cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____90223 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____90223
          then
            let ct1 =
              let uu____90227 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____90227 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____90234 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____90234
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3729_90241 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3729_90241.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3729_90241.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3729_90241.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev
                      cfg.FStar_TypeChecker_Cfg.tcenv c
                     in
                  let uu___3733_90243 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3733_90243.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3733_90243.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3733_90243.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3733_90243.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3736_90244 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3736_90244.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3736_90244.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____90247 -> c
  
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
        let uu____90267 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____90267  in
      let uu____90274 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____90274
      then
        let uu____90277 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____90277 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____90283  ->
                 let uu____90284 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____90284)
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
          (fun uu___3752_90301  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___3751_90304 ->
            ((let uu____90306 =
                let uu____90312 =
                  let uu____90314 = FStar_Util.message_of_exn uu___3751_90304
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____90314
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____90312)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____90306);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          (fun uu___3762_90333  ->
             match () with
             | () ->
                 let uu____90334 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____90334 [] c) ()
        with
        | uu___3761_90343 ->
            ((let uu____90345 =
                let uu____90351 =
                  let uu____90353 = FStar_Util.message_of_exn uu___3761_90343
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____90353
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____90351)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____90345);
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
                   let uu____90402 =
                     let uu____90403 =
                       let uu____90410 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____90410)  in
                     FStar_Syntax_Syntax.Tm_refine uu____90403  in
                   mk uu____90402 t01.FStar_Syntax_Syntax.pos
               | uu____90415 -> t2)
          | uu____90416 -> t2  in
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
        let uu____90510 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____90510 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____90547 ->
                 let uu____90556 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____90556 with
                  | (actuals,uu____90566,uu____90567) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____90587 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____90587 with
                         | (binders,args) ->
                             let uu____90598 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____90598
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
      | uu____90613 ->
          let uu____90614 = FStar_Syntax_Util.head_and_args t  in
          (match uu____90614 with
           | (head1,args) ->
               let uu____90657 =
                 let uu____90658 = FStar_Syntax_Subst.compress head1  in
                 uu____90658.FStar_Syntax_Syntax.n  in
               (match uu____90657 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____90679 =
                      let uu____90694 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____90694  in
                    (match uu____90679 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____90734 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___3832_90742 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3832_90742.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3832_90742.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3832_90742.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3832_90742.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3832_90742.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3832_90742.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3832_90742.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3832_90742.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3832_90742.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___3832_90742.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3832_90742.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3832_90742.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3832_90742.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3832_90742.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3832_90742.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3832_90742.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3832_90742.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3832_90742.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3832_90742.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3832_90742.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3832_90742.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3832_90742.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3832_90742.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3832_90742.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3832_90742.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3832_90742.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3832_90742.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3832_90742.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3832_90742.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3832_90742.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3832_90742.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3832_90742.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3832_90742.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3832_90742.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3832_90742.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___3832_90742.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3832_90742.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3832_90742.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3832_90742.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3832_90742.FStar_TypeChecker_Env.nbe)
                                 }) t
                               in
                            match uu____90734 with
                            | (uu____90745,ty,uu____90747) ->
                                eta_expand_with_type env t ty))
                | uu____90748 ->
                    let uu____90749 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___3839_90757 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3839_90757.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3839_90757.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3839_90757.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3839_90757.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3839_90757.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3839_90757.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3839_90757.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3839_90757.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3839_90757.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___3839_90757.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3839_90757.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3839_90757.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3839_90757.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3839_90757.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3839_90757.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3839_90757.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3839_90757.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3839_90757.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3839_90757.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3839_90757.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3839_90757.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3839_90757.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3839_90757.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3839_90757.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3839_90757.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3839_90757.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3839_90757.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3839_90757.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3839_90757.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3839_90757.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3839_90757.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3839_90757.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3839_90757.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3839_90757.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3839_90757.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___3839_90757.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3839_90757.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3839_90757.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3839_90757.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3839_90757.FStar_TypeChecker_Env.nbe)
                         }) t
                       in
                    (match uu____90749 with
                     | (uu____90760,ty,uu____90762) ->
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
      let uu___3851_90844 = x  in
      let uu____90845 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3851_90844.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3851_90844.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____90845
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____90848 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____90872 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____90873 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____90874 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____90875 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____90882 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____90883 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____90884 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3877_90918 = rc  in
          let uu____90919 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____90928 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3877_90918.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____90919;
            FStar_Syntax_Syntax.residual_flags = uu____90928
          }  in
        let uu____90931 =
          let uu____90932 =
            let uu____90951 = elim_delayed_subst_binders bs  in
            let uu____90960 = elim_delayed_subst_term t2  in
            let uu____90963 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____90951, uu____90960, uu____90963)  in
          FStar_Syntax_Syntax.Tm_abs uu____90932  in
        mk1 uu____90931
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____91000 =
          let uu____91001 =
            let uu____91016 = elim_delayed_subst_binders bs  in
            let uu____91025 = elim_delayed_subst_comp c  in
            (uu____91016, uu____91025)  in
          FStar_Syntax_Syntax.Tm_arrow uu____91001  in
        mk1 uu____91000
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____91044 =
          let uu____91045 =
            let uu____91052 = elim_bv bv  in
            let uu____91053 = elim_delayed_subst_term phi  in
            (uu____91052, uu____91053)  in
          FStar_Syntax_Syntax.Tm_refine uu____91045  in
        mk1 uu____91044
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____91084 =
          let uu____91085 =
            let uu____91102 = elim_delayed_subst_term t2  in
            let uu____91105 = elim_delayed_subst_args args  in
            (uu____91102, uu____91105)  in
          FStar_Syntax_Syntax.Tm_app uu____91085  in
        mk1 uu____91084
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3899_91177 = p  in
              let uu____91178 =
                let uu____91179 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____91179  in
              {
                FStar_Syntax_Syntax.v = uu____91178;
                FStar_Syntax_Syntax.p =
                  (uu___3899_91177.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3903_91181 = p  in
              let uu____91182 =
                let uu____91183 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____91183  in
              {
                FStar_Syntax_Syntax.v = uu____91182;
                FStar_Syntax_Syntax.p =
                  (uu___3903_91181.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3909_91190 = p  in
              let uu____91191 =
                let uu____91192 =
                  let uu____91199 = elim_bv x  in
                  let uu____91200 = elim_delayed_subst_term t0  in
                  (uu____91199, uu____91200)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____91192  in
              {
                FStar_Syntax_Syntax.v = uu____91191;
                FStar_Syntax_Syntax.p =
                  (uu___3909_91190.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3915_91225 = p  in
              let uu____91226 =
                let uu____91227 =
                  let uu____91241 =
                    FStar_List.map
                      (fun uu____91267  ->
                         match uu____91267 with
                         | (x,b) ->
                             let uu____91284 = elim_pat x  in
                             (uu____91284, b)) pats
                     in
                  (fv, uu____91241)  in
                FStar_Syntax_Syntax.Pat_cons uu____91227  in
              {
                FStar_Syntax_Syntax.v = uu____91226;
                FStar_Syntax_Syntax.p =
                  (uu___3915_91225.FStar_Syntax_Syntax.p)
              }
          | uu____91299 -> p  in
        let elim_branch uu____91323 =
          match uu____91323 with
          | (pat,wopt,t3) ->
              let uu____91349 = elim_pat pat  in
              let uu____91352 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____91355 = elim_delayed_subst_term t3  in
              (uu____91349, uu____91352, uu____91355)
           in
        let uu____91360 =
          let uu____91361 =
            let uu____91384 = elim_delayed_subst_term t2  in
            let uu____91387 = FStar_List.map elim_branch branches  in
            (uu____91384, uu____91387)  in
          FStar_Syntax_Syntax.Tm_match uu____91361  in
        mk1 uu____91360
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____91518 =
          match uu____91518 with
          | (tc,topt) ->
              let uu____91553 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____91563 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____91563
                | FStar_Util.Inr c ->
                    let uu____91565 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____91565
                 in
              let uu____91566 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____91553, uu____91566)
           in
        let uu____91575 =
          let uu____91576 =
            let uu____91603 = elim_delayed_subst_term t2  in
            let uu____91606 = elim_ascription a  in
            (uu____91603, uu____91606, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____91576  in
        mk1 uu____91575
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3945_91669 = lb  in
          let uu____91670 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____91673 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3945_91669.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3945_91669.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____91670;
            FStar_Syntax_Syntax.lbeff =
              (uu___3945_91669.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____91673;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3945_91669.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3945_91669.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____91676 =
          let uu____91677 =
            let uu____91691 =
              let uu____91699 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____91699)  in
            let uu____91711 = elim_delayed_subst_term t2  in
            (uu____91691, uu____91711)  in
          FStar_Syntax_Syntax.Tm_let uu____91677  in
        mk1 uu____91676
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____91756 =
          let uu____91757 =
            let uu____91764 = elim_delayed_subst_term tm  in
            (uu____91764, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____91757  in
        mk1 uu____91756
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____91775 =
          let uu____91776 =
            let uu____91783 = elim_delayed_subst_term t2  in
            let uu____91786 = elim_delayed_subst_meta md  in
            (uu____91783, uu____91786)  in
          FStar_Syntax_Syntax.Tm_meta uu____91776  in
        mk1 uu____91775

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
      (fun uu___603_91795  ->
         match uu___603_91795 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____91799 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____91799
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
        let uu____91822 =
          let uu____91823 =
            let uu____91832 = elim_delayed_subst_term t  in
            (uu____91832, uopt)  in
          FStar_Syntax_Syntax.Total uu____91823  in
        mk1 uu____91822
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____91849 =
          let uu____91850 =
            let uu____91859 = elim_delayed_subst_term t  in
            (uu____91859, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____91850  in
        mk1 uu____91849
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3978_91868 = ct  in
          let uu____91869 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____91872 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____91883 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3978_91868.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3978_91868.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____91869;
            FStar_Syntax_Syntax.effect_args = uu____91872;
            FStar_Syntax_Syntax.flags = uu____91883
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___604_91886  ->
    match uu___604_91886 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____91900 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____91900
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____91939 =
          let uu____91946 = elim_delayed_subst_term t  in (m, uu____91946)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____91939
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____91958 =
          let uu____91967 = elim_delayed_subst_term t  in
          (m1, m2, uu____91967)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____91958
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
      (fun uu____92000  ->
         match uu____92000 with
         | (t,q) ->
             let uu____92019 = elim_delayed_subst_term t  in (uu____92019, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____92047  ->
         match uu____92047 with
         | (x,q) ->
             let uu____92066 =
               let uu___4002_92067 = x  in
               let uu____92068 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___4002_92067.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___4002_92067.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____92068
               }  in
             (uu____92066, q)) bs

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
            | (uu____92176,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____92208,FStar_Util.Inl t) ->
                let uu____92230 =
                  let uu____92237 =
                    let uu____92238 =
                      let uu____92253 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____92253)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____92238  in
                  FStar_Syntax_Syntax.mk uu____92237  in
                uu____92230 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____92269 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____92269 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____92301 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____92374 ->
                    let uu____92375 =
                      let uu____92384 =
                        let uu____92385 = FStar_Syntax_Subst.compress t4  in
                        uu____92385.FStar_Syntax_Syntax.n  in
                      (uu____92384, tc)  in
                    (match uu____92375 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____92414) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____92461) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____92506,FStar_Util.Inl uu____92507) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____92538 -> failwith "Impossible")
                 in
              (match uu____92301 with
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
          let uu____92677 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____92677 with
          | (univ_names1,binders1,tc) ->
              let uu____92751 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____92751)
  
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
          let uu____92805 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____92805 with
          | (univ_names1,binders1,tc) ->
              let uu____92879 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____92879)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____92921 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____92921 with
           | (univ_names1,binders1,typ1) ->
               let uu___4085_92961 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4085_92961.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4085_92961.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4085_92961.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4085_92961.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___4091_92976 = s  in
          let uu____92977 =
            let uu____92978 =
              let uu____92987 = FStar_List.map (elim_uvars env) sigs  in
              (uu____92987, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____92978  in
          {
            FStar_Syntax_Syntax.sigel = uu____92977;
            FStar_Syntax_Syntax.sigrng =
              (uu___4091_92976.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___4091_92976.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___4091_92976.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___4091_92976.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____93006 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____93006 with
           | (univ_names1,uu____93030,typ1) ->
               let uu___4105_93052 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4105_93052.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4105_93052.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4105_93052.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4105_93052.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____93059 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____93059 with
           | (univ_names1,uu____93083,typ1) ->
               let uu___4116_93105 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4116_93105.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4116_93105.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4116_93105.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4116_93105.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____93135 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____93135 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____93160 =
                            let uu____93161 =
                              let uu____93162 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____93162  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____93161
                             in
                          elim_delayed_subst_term uu____93160  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___4132_93165 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___4132_93165.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___4132_93165.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___4132_93165.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___4132_93165.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___4135_93166 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___4135_93166.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___4135_93166.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___4135_93166.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___4135_93166.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___4139_93173 = s  in
          let uu____93174 =
            let uu____93175 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____93175  in
          {
            FStar_Syntax_Syntax.sigel = uu____93174;
            FStar_Syntax_Syntax.sigrng =
              (uu___4139_93173.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___4139_93173.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___4139_93173.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___4139_93173.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____93179 = elim_uvars_aux_t env us [] t  in
          (match uu____93179 with
           | (us1,uu____93203,t1) ->
               let uu___4150_93225 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4150_93225.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4150_93225.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4150_93225.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4150_93225.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____93226 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____93229 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____93229 with
           | (univs1,binders,signature) ->
               let uu____93269 =
                 let uu____93274 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____93274 with
                 | (univs_opening,univs2) ->
                     let uu____93297 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____93297)
                  in
               (match uu____93269 with
                | (univs_opening,univs_closing) ->
                    let uu____93300 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____93306 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____93307 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____93306, uu____93307)  in
                    (match uu____93300 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____93333 =
                           match uu____93333 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____93351 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____93351 with
                                | (us1,t1) ->
                                    let uu____93362 =
                                      let uu____93371 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____93382 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____93371, uu____93382)  in
                                    (match uu____93362 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____93411 =
                                           let uu____93420 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____93431 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____93420, uu____93431)  in
                                         (match uu____93411 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____93461 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____93461
                                                 in
                                              let uu____93462 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____93462 with
                                               | (uu____93489,uu____93490,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____93513 =
                                                       let uu____93514 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____93514
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____93513
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____93523 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____93523 with
                           | (uu____93542,uu____93543,t1) -> t1  in
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
                             | uu____93619 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____93646 =
                               let uu____93647 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____93647.FStar_Syntax_Syntax.n  in
                             match uu____93646 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____93706 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____93740 =
                               let uu____93741 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____93741.FStar_Syntax_Syntax.n  in
                             match uu____93740 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____93764) ->
                                 let uu____93789 = destruct_action_body body
                                    in
                                 (match uu____93789 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____93838 ->
                                 let uu____93839 = destruct_action_body t  in
                                 (match uu____93839 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____93894 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____93894 with
                           | (action_univs,t) ->
                               let uu____93903 = destruct_action_typ_templ t
                                  in
                               (match uu____93903 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___4236_93950 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___4236_93950.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___4236_93950.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___4239_93952 = ed  in
                           let uu____93953 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____93954 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____93955 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____93956 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____93957 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____93958 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____93959 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____93960 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____93961 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____93962 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____93963 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____93964 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____93965 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____93966 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___4239_93952.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___4239_93952.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____93953;
                             FStar_Syntax_Syntax.bind_wp = uu____93954;
                             FStar_Syntax_Syntax.if_then_else = uu____93955;
                             FStar_Syntax_Syntax.ite_wp = uu____93956;
                             FStar_Syntax_Syntax.stronger = uu____93957;
                             FStar_Syntax_Syntax.close_wp = uu____93958;
                             FStar_Syntax_Syntax.assert_p = uu____93959;
                             FStar_Syntax_Syntax.assume_p = uu____93960;
                             FStar_Syntax_Syntax.null_wp = uu____93961;
                             FStar_Syntax_Syntax.trivial = uu____93962;
                             FStar_Syntax_Syntax.repr = uu____93963;
                             FStar_Syntax_Syntax.return_repr = uu____93964;
                             FStar_Syntax_Syntax.bind_repr = uu____93965;
                             FStar_Syntax_Syntax.actions = uu____93966;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___4239_93952.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___4242_93969 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___4242_93969.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___4242_93969.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___4242_93969.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___4242_93969.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___605_93990 =
            match uu___605_93990 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____94021 = elim_uvars_aux_t env us [] t  in
                (match uu____94021 with
                 | (us1,uu____94053,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___4257_94084 = sub_eff  in
            let uu____94085 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____94088 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___4257_94084.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___4257_94084.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____94085;
              FStar_Syntax_Syntax.lift = uu____94088
            }  in
          let uu___4260_94091 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___4260_94091.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___4260_94091.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___4260_94091.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___4260_94091.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____94101 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____94101 with
           | (univ_names1,binders1,comp1) ->
               let uu___4273_94141 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4273_94141.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4273_94141.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4273_94141.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4273_94141.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____94144 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____94145 -> s
  
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
        let uu____94194 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____94194 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____94216 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____94216 with
             | (uu____94223,head_def) ->
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
      let uu____94229 = FStar_Syntax_Util.head_and_args t  in
      match uu____94229 with
      | (head1,args) ->
          let uu____94274 =
            let uu____94275 = FStar_Syntax_Subst.compress head1  in
            uu____94275.FStar_Syntax_Syntax.n  in
          (match uu____94274 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____94282;
                  FStar_Syntax_Syntax.vars = uu____94283;_},us)
               -> aux fv us args
           | uu____94289 -> FStar_Pervasives_Native.None)
  