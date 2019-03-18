open Prims
let cases :
  'Auu____59192 'Auu____59193 .
    ('Auu____59192 -> 'Auu____59193) ->
      'Auu____59193 ->
        'Auu____59192 FStar_Pervasives_Native.option -> 'Auu____59193
  =
  fun f  ->
    fun d  ->
      fun uu___585_59213  ->
        match uu___585_59213 with
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
    match projectee with | Clos _0 -> true | uu____59311 -> false
  
let (__proj__Clos__item___0 :
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
      Prims.list * FStar_Syntax_Syntax.term * ((FStar_Syntax_Syntax.binder
      FStar_Pervasives_Native.option * closure) Prims.list *
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool))
  = fun projectee  -> match projectee with | Clos _0 -> _0 
let (uu___is_Univ : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____59423 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____59441 -> false
  
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
    match projectee with | Arg _0 -> true | uu____59610 -> false
  
let (__proj__Arg__item___0 :
  stack_elt -> (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)) =
  fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____59653 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range))
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____59696 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo) =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____59741 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env * branches * FStar_TypeChecker_Cfg.cfg * FStar_Range.range))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____59796 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * env *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
      FStar_Range.range))
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____59859 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Range.range))
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____59908 -> false
  
let (__proj__Meta__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.metadata * FStar_Range.range)) =
  fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____59953 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding *
      FStar_Range.range))
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____59996 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> FStar_TypeChecker_Cfg.cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____60019 -> false
  
let (__proj__Debug__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.term * FStar_Util.time)) =
  fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____60048 = FStar_Syntax_Util.head_and_args' t  in
    match uu____60048 with | (hd1,uu____60064) -> hd1
  
let mk :
  'Auu____60092 .
    'Auu____60092 ->
      FStar_Range.range -> 'Auu____60092 FStar_Syntax_Syntax.syntax
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
          let uu____60135 = FStar_ST.op_Bang r  in
          match uu____60135 with
          | FStar_Pervasives_Native.Some uu____60161 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____60216 =
      FStar_List.map
        (fun uu____60232  ->
           match uu____60232 with
           | (bopt,c) ->
               let uu____60246 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____60251 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____60246 uu____60251) env
       in
    FStar_All.pipe_right uu____60216 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___586_60259  ->
    match uu___586_60259 with
    | Clos (env,t,uu____60263,uu____60264) ->
        let uu____60311 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____60321 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____60311 uu____60321
    | Univ uu____60324 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___587_60333  ->
    match uu___587_60333 with
    | Arg (c,uu____60336,uu____60337) ->
        let uu____60338 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____60338
    | MemoLazy uu____60341 -> "MemoLazy"
    | Abs (uu____60349,bs,uu____60351,uu____60352,uu____60353) ->
        let uu____60358 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____60358
    | UnivArgs uu____60369 -> "UnivArgs"
    | Match uu____60377 -> "Match"
    | App (uu____60387,t,uu____60389,uu____60390) ->
        let uu____60391 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____60391
    | Meta (uu____60394,m,uu____60396) -> "Meta"
    | Let uu____60398 -> "Let"
    | Cfg uu____60408 -> "Cfg"
    | Debug (t,uu____60411) ->
        let uu____60412 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____60412
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____60426 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____60426 (FStar_String.concat "; ")
  
let is_empty : 'Auu____60441 . 'Auu____60441 Prims.list -> Prims.bool =
  fun uu___588_60449  ->
    match uu___588_60449 with | [] -> true | uu____60453 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        (fun uu___700_60486  ->
           match () with
           | () ->
               let uu____60487 =
                 FStar_List.nth env x.FStar_Syntax_Syntax.index  in
               FStar_Pervasives_Native.snd uu____60487) ()
      with
      | uu___699_60504 ->
          let uu____60505 =
            let uu____60507 = FStar_Syntax_Print.db_to_string x  in
            let uu____60509 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____60507
              uu____60509
             in
          failwith uu____60505
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____60520 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____60520
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____60527 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____60527
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____60534 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____60534
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
          let uu____60572 =
            FStar_List.fold_left
              (fun uu____60598  ->
                 fun u1  ->
                   match uu____60598 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____60623 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____60623 with
                        | (k_u,n1) ->
                            let uu____60641 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____60641
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____60572 with
          | (uu____60662,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 (fun uu___734_60688  ->
                    match () with
                    | () ->
                        let uu____60691 =
                          let uu____60692 = FStar_List.nth env x  in
                          FStar_Pervasives_Native.snd uu____60692  in
                        (match uu____60691 with
                         | Univ u3 ->
                             ((let uu____60711 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      cfg.FStar_TypeChecker_Cfg.tcenv)
                                   (FStar_Options.Other "univ_norm")
                                  in
                               if uu____60711
                               then
                                 let uu____60716 =
                                   FStar_Syntax_Print.univ_to_string u3  in
                                 FStar_Util.print1
                                   "Univ (in norm_universe): %s\n"
                                   uu____60716
                               else ());
                              aux u3)
                         | Dummy  -> [u2]
                         | uu____60721 ->
                             let uu____60722 =
                               let uu____60724 = FStar_Util.string_of_int x
                                  in
                               FStar_Util.format1
                                 "Impossible: universe variable u@%s bound to a term"
                                 uu____60724
                                in
                             failwith uu____60722)) ()
               with
               | uu____60734 ->
                   if
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else
                     (let uu____60740 =
                        let uu____60742 = FStar_Util.string_of_int x  in
                        FStar_String.op_Hat "Universe variable not found: u@"
                          uu____60742
                         in
                      failwith uu____60740))
          | FStar_Syntax_Syntax.U_unif uu____60747 when
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____60756 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____60765 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____60772 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____60772 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____60789 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____60789 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____60800 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____60810 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____60810 with
                                  | (uu____60817,m) -> n1 <= m))
                           in
                        if uu____60800 then rest1 else us1
                    | uu____60826 -> us1)
               | uu____60832 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____60836 = aux u3  in
              FStar_List.map
                (fun _60839  -> FStar_Syntax_Syntax.U_succ _60839)
                uu____60836
           in
        if
          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____60843 = aux u  in
           match uu____60843 with
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
            (fun uu____61012  ->
               let uu____61013 = FStar_Syntax_Print.tag_of_term t  in
               let uu____61015 = env_to_string env  in
               let uu____61017 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____61013 uu____61015 uu____61017);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____61030 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____61033 ->
                    let uu____61056 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____61056
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____61057 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____61058 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____61059 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____61060 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____61085 ->
                           let uu____61098 =
                             let uu____61100 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____61102 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____61100 uu____61102
                              in
                           failwith uu____61098
                       | uu____61107 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___589_61143  ->
                                         match uu___589_61143 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____61150 =
                                               let uu____61157 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____61157)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____61150
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___828_61169 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___828_61169.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___828_61169.FStar_Syntax_Syntax.sort)
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
                                              | uu____61175 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____61178 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___837_61183 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___837_61183.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___837_61183.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____61204 =
                        let uu____61205 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____61205  in
                      mk uu____61204 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____61213 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____61213  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____61215 = lookup_bvar env x  in
                    (match uu____61215 with
                     | Univ uu____61218 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___853_61223 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___853_61223.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___853_61223.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____61229,uu____61230) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____61321  ->
                              fun stack1  ->
                                match uu____61321 with
                                | (a,aq) ->
                                    let uu____61333 =
                                      let uu____61334 =
                                        let uu____61341 =
                                          let uu____61342 =
                                            let uu____61374 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____61374, false)  in
                                          Clos uu____61342  in
                                        (uu____61341, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____61334  in
                                    uu____61333 :: stack1) args)
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
                    let uu____61542 = close_binders cfg env bs  in
                    (match uu____61542 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,uu____61592) when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    ->
                    inline_closure_env cfg env stack
                      x.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____61603 =
                      let uu____61616 =
                        let uu____61625 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____61625]  in
                      close_binders cfg env uu____61616  in
                    (match uu____61603 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____61670 =
                             let uu____61671 =
                               let uu____61678 =
                                 let uu____61679 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____61679
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____61678, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____61671  in
                           mk uu____61670 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____61778 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____61778
                      | FStar_Util.Inr c ->
                          let uu____61792 = close_comp cfg env c  in
                          FStar_Util.Inr uu____61792
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____61811 =
                        let uu____61812 =
                          let uu____61839 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____61839, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____61812  in
                      mk uu____61811 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____61885 =
                            let uu____61886 =
                              let uu____61893 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____61893, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____61886  in
                          mk uu____61885 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____61948  -> dummy :: env1) env
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
                    let uu____61969 =
                      let uu____61980 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____61980
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____62002 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___945_62018 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___945_62018.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___945_62018.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____62002))
                       in
                    (match uu____61969 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___950_62036 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___950_62036.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___950_62036.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___950_62036.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___950_62036.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____62053,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____62119  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____62136 =
                          FStar_Syntax_Syntax.is_top_level lbs  in
                        if uu____62136
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____62151  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____62175 =
                          FStar_Syntax_Syntax.is_top_level lbs  in
                        if uu____62175
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___973_62186 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___973_62186.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___973_62186.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___976_62187 = lb  in
                      let uu____62188 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___976_62187.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___976_62187.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____62188;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___976_62187.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___976_62187.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____62220  -> fun env1  -> dummy :: env1)
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
            (fun uu____62312  ->
               let uu____62313 = FStar_Syntax_Print.tag_of_term t  in
               let uu____62315 = env_to_string env  in
               let uu____62317 = stack_to_string stack  in
               let uu____62319 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____62313 uu____62315 uu____62317 uu____62319);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____62326,uu____62327),aq,r))::stack1
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
               let uu____62408 = close_binders cfg env' bs  in
               (match uu____62408 with
                | (bs1,uu____62424) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____62444 =
                      let uu___1034_62447 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___1034_62447.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___1034_62447.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____62444)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____62503 =
                 match uu____62503 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____62618 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____62649 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____62738  ->
                                     fun uu____62739  ->
                                       match (uu____62738, uu____62739) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____62889 = norm_pat env4 p1
                                              in
                                           (match uu____62889 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____62649 with
                            | (pats1,env4) ->
                                ((let uu___1071_63059 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___1071_63059.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___1075_63080 = x  in
                             let uu____63081 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1075_63080.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1075_63080.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____63081
                             }  in
                           ((let uu___1078_63095 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___1078_63095.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___1082_63106 = x  in
                             let uu____63107 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1082_63106.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1082_63106.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____63107
                             }  in
                           ((let uu___1085_63121 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___1085_63121.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___1091_63137 = x  in
                             let uu____63138 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1091_63137.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1091_63137.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____63138
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___1095_63155 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___1095_63155.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____63160 = norm_pat env2 pat  in
                     (match uu____63160 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____63229 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____63229
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____63248 =
                   let uu____63249 =
                     let uu____63272 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____63272)  in
                   FStar_Syntax_Syntax.Tm_match uu____63249  in
                 mk uu____63248 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern args ->
                     let uu____63387 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun args1  ->
                               FStar_All.pipe_right args1
                                 (FStar_List.map
                                    (fun uu____63496  ->
                                       match uu____63496 with
                                       | (a,q) ->
                                           let uu____63523 =
                                             non_tail_inline_closure_env cfg
                                               env_m a
                                              in
                                           (uu____63523, q)))))
                        in
                     FStar_Syntax_Syntax.Meta_pattern uu____63387
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____63536 =
                       let uu____63543 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____63543)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____63536
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____63555 =
                       let uu____63564 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____63564)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____63555
                 | uu____63569 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____63575 -> failwith "Impossible: unexpected stack element")

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
            let uu____63591 =
              let uu____63592 = inline_closure_env cfg env [] t  in
              FStar_Syntax_Syntax.Meta uu____63592  in
            FStar_Pervasives_Native.Some uu____63591
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
        let uu____63609 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____63693  ->
                  fun uu____63694  ->
                    match (uu____63693, uu____63694) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___1148_63834 = b  in
                          let uu____63835 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1148_63834.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1148_63834.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____63835
                          }  in
                        let imp1 = close_imp cfg env1 imp  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp1) :: out))) (env, []))
           in
        match uu____63609 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____63977 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____63990 = inline_closure_env cfg env [] t  in
                 let uu____63991 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____63990 uu____63991
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____64004 = inline_closure_env cfg env [] t  in
                 let uu____64005 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____64004 uu____64005
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____64059  ->
                           match uu____64059 with
                           | (a,q) ->
                               let uu____64080 =
                                 inline_closure_env cfg env [] a  in
                               (uu____64080, q)))
                    in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___590_64097  ->
                           match uu___590_64097 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____64101 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____64101
                           | f -> f))
                    in
                 let uu____64105 =
                   let uu___1181_64106 = c1  in
                   let uu____64107 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____64107;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___1181_64106.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____64105)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___591_64117  ->
            match uu___591_64117 with
            | FStar_Syntax_Syntax.DECREASES uu____64119 -> false
            | uu____64123 -> true))

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
                   (fun uu___592_64142  ->
                      match uu___592_64142 with
                      | FStar_Syntax_Syntax.DECREASES uu____64144 -> false
                      | uu____64148 -> true))
               in
            let rc1 =
              let uu___1198_64151 = rc  in
              let uu____64152 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___1198_64151.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____64152;
                FStar_Syntax_Syntax.residual_flags = flags
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____64161 -> lopt

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
    let uu____64209 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____64209 with
    | FStar_Pervasives_Native.Some e ->
        let uu____64248 = FStar_Syntax_Embeddings.unembed e t  in
        uu____64248 true FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____64268 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv * 'Auu____64268)
        FStar_Pervasives_Native.option * closure) Prims.list ->
        FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____64330  ->
           fun subst1  ->
             match uu____64330 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____64371,uu____64372)) ->
                      let uu____64433 = b  in
                      (match uu____64433 with
                       | (bv,uu____64441) ->
                           let uu____64442 =
                             let uu____64444 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____64444  in
                           if uu____64442
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____64452 = unembed_binder term1  in
                              match uu____64452 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____64459 =
                                      let uu___1233_64460 = bv  in
                                      let uu____64461 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___1233_64460.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___1233_64460.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort =
                                          uu____64461
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv
                                      uu____64459
                                     in
                                  let b_for_x =
                                    let uu____64467 =
                                      let uu____64474 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____64474)
                                       in
                                    FStar_Syntax_Syntax.NT uu____64467  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___593_64490  ->
                                         match uu___593_64490 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____64492,{
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_name
                                                              b';
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____64494;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____64495;_})
                                             ->
                                             let uu____64500 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____64500
                                         | uu____64502 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____64504 -> subst1)) env []
  
let reduce_primops :
  'Auu____64526 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'Auu____64526)
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
            (let uu____64578 = FStar_Syntax_Util.head_and_args tm  in
             match uu____64578 with
             | (head1,args) ->
                 let uu____64623 =
                   let uu____64624 = FStar_Syntax_Util.un_uinst head1  in
                   uu____64624.FStar_Syntax_Syntax.n  in
                 (match uu____64623 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____64630 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                      (match uu____64630 with
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
                                (fun uu____64653  ->
                                   let uu____64654 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name
                                      in
                                   let uu____64656 =
                                     FStar_Util.string_of_int l  in
                                   let uu____64658 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____64654 uu____64656 uu____64658);
                              tm)
                           else
                             (let uu____64663 =
                                if l = prim_step.FStar_TypeChecker_Cfg.arity
                                then (args, [])
                                else
                                  FStar_List.splitAt
                                    prim_step.FStar_TypeChecker_Cfg.arity
                                    args
                                 in
                              match uu____64663 with
                              | (args_1,args_2) ->
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____64749  ->
                                        let uu____64750 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____64750);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____64755  ->
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
                                           (fun uu____64769  ->
                                              let uu____64770 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____64770);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____64778  ->
                                              let uu____64779 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____64781 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____64779 uu____64781);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____64784 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____64788  ->
                                 let uu____64789 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____64789);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____64795  ->
                            let uu____64796 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____64796);
                       (match args with
                        | (a1,uu____64802)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____64827 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____64841  ->
                            let uu____64842 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____64842);
                       (match args with
                        | (t,uu____64848)::(r,uu____64850)::[] ->
                            let uu____64891 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____64891 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____64897 -> tm))
                  | uu____64908 -> tm))
  
let reduce_equality :
  'Auu____64919 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'Auu____64919)
          FStar_Pervasives_Native.option * closure) Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun tm  ->
        reduce_primops norm_cb
          (let uu___1321_64968 = cfg  in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___1323_64971 = FStar_TypeChecker_Cfg.default_steps  in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.nbe_step);
                  FStar_TypeChecker_Cfg.for_extraction =
                    (uu___1323_64971.FStar_TypeChecker_Cfg.for_extraction)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___1321_64968.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___1321_64968.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___1321_64968.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___1321_64968.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___1321_64968.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___1321_64968.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___1321_64968.FStar_TypeChecker_Cfg.reifying)
           }) tm
  
type norm_request_t =
  | Norm_request_none 
  | Norm_request_ready 
  | Norm_request_requires_rejig 
let (uu___is_Norm_request_none : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_none  -> true | uu____64982 -> false
  
let (uu___is_Norm_request_ready : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_ready  -> true | uu____64993 -> false
  
let (uu___is_Norm_request_requires_rejig : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Norm_request_requires_rejig  -> true
    | uu____65004 -> false
  
let (is_norm_request :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.args -> norm_request_t) =
  fun hd1  ->
    fun args  ->
      let aux min_args =
        let uu____65025 = FStar_All.pipe_right args FStar_List.length  in
        FStar_All.pipe_right uu____65025
          (fun n1  ->
             if n1 < min_args
             then Norm_request_none
             else
               if n1 = min_args
               then Norm_request_ready
               else Norm_request_requires_rejig)
         in
      let uu____65057 =
        let uu____65058 = FStar_Syntax_Util.un_uinst hd1  in
        uu____65058.FStar_Syntax_Syntax.n  in
      match uu____65057 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          -> aux (Prims.parse_int "2")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          aux (Prims.parse_int "1")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          aux (Prims.parse_int "3")
      | uu____65067 -> Norm_request_none
  
let (should_consider_norm_requests : FStar_TypeChecker_Cfg.cfg -> Prims.bool)
  =
  fun cfg  ->
    (Prims.op_Negation
       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
      &&
      (let uu____65076 =
         FStar_Ident.lid_equals
           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
           FStar_Parser_Const.prims_lid
          in
       Prims.op_Negation uu____65076)
  
let (rejig_norm_request :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term)
  =
  fun hd1  ->
    fun args  ->
      let uu____65089 =
        let uu____65090 = FStar_Syntax_Util.un_uinst hd1  in
        uu____65090.FStar_Syntax_Syntax.n  in
      match uu____65089 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          ->
          (match args with
           | t1::t2::rest when
               (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____65148 = FStar_Syntax_Util.mk_app hd1 [t1; t2]  in
               FStar_Syntax_Util.mk_app uu____65148 rest
           | uu____65175 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize_term")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          (match args with
           | t::rest when (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____65215 = FStar_Syntax_Util.mk_app hd1 [t]  in
               FStar_Syntax_Util.mk_app uu____65215 rest
           | uu____65234 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          (match args with
           | t1::t2::t3::rest when
               (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____65308 = FStar_Syntax_Util.mk_app hd1 [t1; t2; t3]
                  in
               FStar_Syntax_Util.mk_app uu____65308 rest
           | uu____65343 ->
               failwith "Impossible! invalid rejig_norm_request for norm")
      | uu____65345 ->
          let uu____65346 =
            let uu____65348 = FStar_Syntax_Print.term_to_string hd1  in
            FStar_String.op_Hat
              "Impossible! invalid rejig_norm_request for: %s" uu____65348
             in
          failwith uu____65346
  
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s  ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
  
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___594_65369  ->
    match uu___594_65369 with
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
        let uu____65376 =
          let uu____65379 =
            let uu____65380 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            FStar_TypeChecker_Env.UnfoldOnly uu____65380  in
          [uu____65379]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____65376
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____65388 =
          let uu____65391 =
            let uu____65392 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            FStar_TypeChecker_Env.UnfoldFully uu____65392  in
          [uu____65391]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____65388
    | FStar_Syntax_Embeddings.UnfoldAttr names1 ->
        let uu____65400 =
          let uu____65403 =
            let uu____65404 = FStar_List.map FStar_Ident.lid_of_str names1
               in
            FStar_TypeChecker_Env.UnfoldAttr uu____65404  in
          [uu____65403]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____65400
    | FStar_Syntax_Embeddings.NBE  -> [FStar_TypeChecker_Env.NBE]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  = fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____65429 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term * 'Auu____65429) Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list * FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____65480 =
            let uu____65485 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____65485 s  in
          match uu____65480 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____65501 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____65501
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
        | uu____65536::(tm,uu____65538)::[] ->
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
        | (tm,uu____65567)::[] ->
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
        | (steps,uu____65588)::uu____65589::(tm,uu____65591)::[] ->
            let add_exclude s z =
              let uu____65629 =
                FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s  in
              if uu____65629
              then s
              else (FStar_TypeChecker_Env.Exclude z) :: s  in
            let uu____65636 =
              let uu____65641 = full_norm steps  in parse_steps uu____65641
               in
            (match uu____65636 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = FStar_TypeChecker_Env.Beta :: s  in
                 let s2 = add_exclude s1 FStar_TypeChecker_Env.Zeta  in
                 let s3 = add_exclude s2 FStar_TypeChecker_Env.Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____65680 -> FStar_Pervasives_Native.None
  
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun s  ->
      fun tm  ->
        let delta_level =
          let uu____65712 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___595_65719  ->
                    match uu___595_65719 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____65721 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____65723 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____65727 -> true
                    | uu____65731 -> false))
             in
          if uu____65712
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta]  in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____65741  ->
             let uu____65742 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____65742);
        (let tm_norm =
           let uu____65746 =
             let uu____65761 = FStar_TypeChecker_Cfg.cfg_env cfg  in
             uu____65761.FStar_TypeChecker_Env.nbe  in
           uu____65746 s cfg.FStar_TypeChecker_Cfg.tcenv tm  in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____65765  ->
              let uu____65766 = FStar_Syntax_Print.term_to_string tm_norm  in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____65766);
         tm_norm)
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___596_65777  ->
    match uu___596_65777 with
    | (App
        (uu____65781,{
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify );
                       FStar_Syntax_Syntax.pos = uu____65782;
                       FStar_Syntax_Syntax.vars = uu____65783;_},uu____65784,uu____65785))::uu____65786
        -> true
    | uu____65792 -> false
  
let firstn :
  'Auu____65803 .
    Prims.int ->
      'Auu____65803 Prims.list ->
        ('Auu____65803 Prims.list * 'Auu____65803 Prims.list)
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack  ->
      let rec drop_irrel uu___597_65860 =
        match uu___597_65860 with
        | (MemoLazy uu____65865)::s -> drop_irrel s
        | (UnivArgs uu____65875)::s -> drop_irrel s
        | s -> s  in
      let uu____65888 = drop_irrel stack  in
      match uu____65888 with
      | (App
          (uu____65892,{
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_reify );
                         FStar_Syntax_Syntax.pos = uu____65893;
                         FStar_Syntax_Syntax.vars = uu____65894;_},uu____65895,uu____65896))::uu____65897
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____65902 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____65931) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____65941) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____65962  ->
                  match uu____65962 with
                  | (a,uu____65973) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____65984 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____66009 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____66011 -> false
    | FStar_Syntax_Syntax.Tm_type uu____66025 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____66027 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____66029 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____66031 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____66033 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____66036 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____66044 -> false
    | FStar_Syntax_Syntax.Tm_let uu____66052 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____66067 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____66087 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____66103 -> true
    | FStar_Syntax_Syntax.Tm_match uu____66111 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____66183  ->
                   match uu____66183 with
                   | (a,uu____66194) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____66205) ->
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
                     (fun uu____66337  ->
                        match uu____66337 with
                        | (a,uu____66348) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____66357,uu____66358,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____66364,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____66370 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____66380 -> false
            | FStar_Syntax_Syntax.Meta_named uu____66382 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____66393 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____66404 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Should_unfold_fully  -> true
    | uu____66415 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Should_unfold_reify  -> true
    | uu____66426 -> false
  
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
            let uu____66459 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo
               in
            match uu____66459 with
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
              (fun uu____66658  ->
                 fun uu____66659  ->
                   match (uu____66658, uu____66659) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____66765 =
            match uu____66765 with
            | (x,y,z) ->
                let uu____66785 = FStar_Util.string_of_bool x  in
                let uu____66787 = FStar_Util.string_of_bool y  in
                let uu____66789 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____66785 uu____66787
                  uu____66789
             in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg  in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____66817  ->
                    let uu____66818 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____66820 = FStar_Util.string_of_bool b  in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____66818 uu____66820);
               if b then reif else no)
            else
              if
                (let uu____66835 =
                   FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                 FStar_Option.isSome uu____66835)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____66840  ->
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
                          ((is_rec,uu____66875),uu____66876);
                        FStar_Syntax_Syntax.sigrng = uu____66877;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____66879;
                        FStar_Syntax_Syntax.sigattrs = uu____66880;_},uu____66881),uu____66882),uu____66883,uu____66884,uu____66885)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____66992  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____66994,uu____66995,uu____66996,uu____66997) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____67064  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____67067),uu____67068);
                        FStar_Syntax_Syntax.sigrng = uu____67069;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____67071;
                        FStar_Syntax_Syntax.sigattrs = uu____67072;_},uu____67073),uu____67074),uu____67075,uu____67076,uu____67077)
                     when
                     is_rec &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____67184  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____67186,FStar_Pervasives_Native.Some
                    uu____67187,uu____67188,uu____67189) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____67257  ->
                           let uu____67258 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____67258);
                      (let uu____67261 =
                         let uu____67273 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____67299 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____67299
                            in
                         let uu____67311 =
                           let uu____67323 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____67349 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____67349
                              in
                           let uu____67365 =
                             let uu____67377 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____67403 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____67403
                                in
                             [uu____67377]  in
                           uu____67323 :: uu____67365  in
                         uu____67273 :: uu____67311  in
                       comb_or uu____67261))
                 | (uu____67451,uu____67452,FStar_Pervasives_Native.Some
                    uu____67453,uu____67454) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____67522  ->
                           let uu____67523 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____67523);
                      (let uu____67526 =
                         let uu____67538 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____67564 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____67564
                            in
                         let uu____67576 =
                           let uu____67588 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____67614 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____67614
                              in
                           let uu____67630 =
                             let uu____67642 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____67668 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____67668
                                in
                             [uu____67642]  in
                           uu____67588 :: uu____67630  in
                         uu____67538 :: uu____67576  in
                       comb_or uu____67526))
                 | (uu____67716,uu____67717,uu____67718,FStar_Pervasives_Native.Some
                    uu____67719) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____67787  ->
                           let uu____67788 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____67788);
                      (let uu____67791 =
                         let uu____67803 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____67829 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____67829
                            in
                         let uu____67841 =
                           let uu____67853 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____67879 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____67879
                              in
                           let uu____67895 =
                             let uu____67907 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____67933 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____67933
                                in
                             [uu____67907]  in
                           uu____67853 :: uu____67895  in
                         uu____67803 :: uu____67841  in
                       comb_or uu____67791))
                 | uu____67981 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____68027  ->
                           let uu____68028 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____68030 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____68032 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level
                              in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____68028 uu____68030 uu____68032);
                      (let uu____68035 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___598_68041  ->
                                 match uu___598_68041 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.InliningDelta  ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____68047 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv
                                        in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____68047 l))
                          in
                       FStar_All.pipe_left yesno uu____68035)))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____68063  ->
               let uu____68064 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____68066 =
                 let uu____68068 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____68068  in
               let uu____68069 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____68064 uu____68066 uu____68069);
          (match res with
           | (false ,uu____68072,uu____68073) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____68098 ->
               let uu____68108 =
                 let uu____68110 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____68110
                  in
               FStar_All.pipe_left failwith uu____68108)
  
let decide_unfolding :
  'Auu____68129 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'Auu____68129 ->
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
                    let uu___1740_68198 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___1742_68201 =
                           cfg.FStar_TypeChecker_Cfg.steps  in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1742_68201.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1742_68201.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1742_68201.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1742_68201.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1742_68201.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1742_68201.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1742_68201.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___1742_68201.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1742_68201.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1742_68201.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1742_68201.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1742_68201.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1742_68201.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1742_68201.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1742_68201.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1742_68201.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1742_68201.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1742_68201.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___1742_68201.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1742_68201.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1742_68201.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1742_68201.FStar_TypeChecker_Cfg.for_extraction)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1740_68198.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1740_68198.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___1740_68198.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1740_68198.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1740_68198.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1740_68198.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1740_68198.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1740_68198.FStar_TypeChecker_Cfg.reifying)
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
                        let uu____68263 = push1 e t  in (UnivArgs (us, r)) ::
                          uu____68263
                    | h::t -> e :: h :: t  in
                  let ref =
                    let uu____68275 =
                      let uu____68282 =
                        let uu____68283 =
                          let uu____68284 = FStar_Syntax_Syntax.lid_of_fv fv
                             in
                          FStar_Const.Const_reflect uu____68284  in
                        FStar_Syntax_Syntax.Tm_constant uu____68283  in
                      FStar_Syntax_Syntax.mk uu____68282  in
                    uu____68275 FStar_Pervasives_Native.None
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
    let uu____68350 =
      let uu____68351 = FStar_Syntax_Subst.compress t  in
      uu____68351.FStar_Syntax_Syntax.n  in
    match uu____68350 with
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____68382 =
          let uu____68383 = FStar_Syntax_Util.un_uinst hd1  in
          uu____68383.FStar_Syntax_Syntax.n  in
        (match uu____68382 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStar_List.length args) = (Prims.parse_int "3"))
             ->
             let f =
               let uu____68400 =
                 let uu____68407 =
                   let uu____68418 = FStar_All.pipe_right args FStar_List.tl
                      in
                   FStar_All.pipe_right uu____68418 FStar_List.tl  in
                 FStar_All.pipe_right uu____68407 FStar_List.hd  in
               FStar_All.pipe_right uu____68400 FStar_Pervasives_Native.fst
                in
             FStar_Pervasives_Native.Some f
         | uu____68517 -> FStar_Pervasives_Native.None)
    | uu____68518 -> FStar_Pervasives_Native.None
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____68797 ->
                   let uu____68820 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____68820
               | uu____68823 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____68833  ->
               let uu____68834 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____68836 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____68838 = FStar_Syntax_Print.term_to_string t1  in
               let uu____68840 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____68848 =
                 let uu____68850 =
                   let uu____68853 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____68853
                    in
                 stack_to_string uu____68850  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____68834 uu____68836 uu____68838 uu____68840 uu____68848);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____68881  ->
               let uu____68882 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____68882);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____68888  ->
                     let uu____68889 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____68889);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____68892 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____68896  ->
                     let uu____68897 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____68897);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____68900 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____68904  ->
                     let uu____68905 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____68905);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____68908 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____68912  ->
                     let uu____68913 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____68913);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____68916;
                 FStar_Syntax_Syntax.fv_delta = uu____68917;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____68921  ->
                     let uu____68922 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____68922);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____68925;
                 FStar_Syntax_Syntax.fv_delta = uu____68926;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____68927);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____68937  ->
                     let uu____68938 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____68938);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid
                  in
               let uu____68944 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
               (match uu____68944 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level _68947) when
                    _68947 = (Prims.parse_int "0") ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____68951  ->
                          let uu____68952 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____68952);
                     rebuild cfg env stack t1)
                | uu____68955 ->
                    let uu____68958 =
                      decide_unfolding cfg env stack
                        t1.FStar_Syntax_Syntax.pos fv qninfo
                       in
                    (match uu____68958 with
                     | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                         do_unfold_fv cfg1 env stack1 t1 qninfo fv
                     | FStar_Pervasives_Native.None  ->
                         rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_quoted uu____68985 ->
               let uu____68992 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____68992
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____69020 = is_norm_request hd1 args  in
                  uu____69020 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu____69026 = rejig_norm_request hd1 args  in
                 norm cfg env stack uu____69026))
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____69054 = is_norm_request hd1 args  in
                  uu____69054 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___1850_69061 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1852_69064 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1852_69064.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1852_69064.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1852_69064.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___1852_69064.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1852_69064.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1852_69064.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1852_69064.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1852_69064.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1852_69064.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1852_69064.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1852_69064.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1852_69064.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1852_69064.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1852_69064.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1852_69064.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1852_69064.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1852_69064.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1852_69064.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1852_69064.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1852_69064.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1852_69064.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1852_69064.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1852_69064.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1850_69061.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1850_69061.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1850_69061.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1850_69061.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1850_69061.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1850_69061.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____69071 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____69071 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____69107  ->
                                 fun stack1  ->
                                   match uu____69107 with
                                   | (a,aq) ->
                                       let uu____69119 =
                                         let uu____69120 =
                                           let uu____69127 =
                                             let uu____69128 =
                                               let uu____69160 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____69160, false)
                                                in
                                             Clos uu____69128  in
                                           (uu____69127, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____69120  in
                                       uu____69119 :: stack1) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____69228  ->
                            let uu____69229 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____69229);
                       norm cfg env stack1 hd1))
                 | FStar_Pervasives_Native.Some (s,tm) when is_nbe_request s
                     ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____69256 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting NBE request on %s ... \n" uu____69256)
                      else ();
                      (let tm' = closure_as_term cfg env tm  in
                       let start = FStar_Util.now ()  in
                       let tm_norm = nbe_eval cfg s tm'  in
                       let fin = FStar_Util.now ()  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         (let uu____69267 =
                            let uu____69269 =
                              let uu____69271 =
                                FStar_Util.time_diff start fin  in
                              FStar_Pervasives_Native.snd uu____69271  in
                            FStar_Util.string_of_int uu____69269  in
                          let uu____69278 =
                            FStar_Syntax_Print.term_to_string tm'  in
                          let uu____69280 =
                            FStar_Syntax_Print.term_to_string tm_norm  in
                          FStar_Util.print3 "NBE'd (%s ms) %s\n\tto %s\n"
                            uu____69267 uu____69278 uu____69280)
                       else ();
                       norm cfg env stack tm_norm))
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____69299 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting norm request on %s ... \n" uu____69299)
                      else ();
                      (let delta_level =
                         let uu____69307 =
                           FStar_All.pipe_right s
                             (FStar_Util.for_some
                                (fun uu___599_69314  ->
                                   match uu___599_69314 with
                                   | FStar_TypeChecker_Env.UnfoldUntil
                                       uu____69316 -> true
                                   | FStar_TypeChecker_Env.UnfoldOnly
                                       uu____69318 -> true
                                   | FStar_TypeChecker_Env.UnfoldFully
                                       uu____69322 -> true
                                   | uu____69326 -> false))
                            in
                         if uu____69307
                         then
                           [FStar_TypeChecker_Env.Unfold
                              FStar_Syntax_Syntax.delta_constant]
                         else [FStar_TypeChecker_Env.NoDelta]  in
                       let cfg'1 =
                         let uu___1893_69334 = cfg  in
                         let uu____69335 =
                           let uu___1895_69336 =
                             FStar_TypeChecker_Cfg.to_fsteps s  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.unfold_only);
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               true;
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___1895_69336.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         {
                           FStar_TypeChecker_Cfg.steps = uu____69335;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___1893_69334.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___1893_69334.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = delta_level;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___1893_69334.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong =
                             (uu___1893_69334.FStar_TypeChecker_Cfg.strong);
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___1893_69334.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___1893_69334.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let stack' =
                         let tail1 = (Cfg cfg) :: stack  in
                         if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           let uu____69344 =
                             let uu____69345 =
                               let uu____69350 = FStar_Util.now ()  in
                               (t1, uu____69350)  in
                             Debug uu____69345  in
                           uu____69344 :: tail1
                         else tail1  in
                       norm cfg'1 env stack' tm))))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____69355 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____69355
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____69366 =
                      let uu____69373 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____69373, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____69366  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____69382 = lookup_bvar env x  in
               (match uu____69382 with
                | Univ uu____69383 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                    then
                      let uu____69437 = FStar_ST.op_Bang r  in
                      (match uu____69437 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____69533  ->
                                 let uu____69534 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____69536 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____69534
                                   uu____69536);
                            (let uu____69539 = maybe_weakly_reduced t'  in
                             if uu____69539
                             then
                               match stack with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____69542 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____69586)::uu____69587 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____69598,uu____69599))::stack_rest ->
                    (match c with
                     | Univ uu____69603 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____69612 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____69642  ->
                                    let uu____69643 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____69643);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____69679  ->
                                    let uu____69680 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____69680);
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
                       (fun uu____69728  ->
                          let uu____69729 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____69729);
                     norm cfg env stack1 t1)
                | (Match uu____69732)::uu____69733 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____69748 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____69748 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____69784  -> dummy :: env1) env)
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
                                          let uu____69828 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____69828)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_69836 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_69836.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_69836.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____69837 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____69843  ->
                                 let uu____69844 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____69844);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_69859 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_69859.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_69859.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_69859.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_69859.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_69859.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_69859.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_69859.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_69859.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____69863)::uu____69864 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____69875 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____69875 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____69911  -> dummy :: env1) env)
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
                                          let uu____69955 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____69955)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_69963 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_69963.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_69963.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____69964 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____69970  ->
                                 let uu____69971 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____69971);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_69986 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_69986.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_69986.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_69986.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_69986.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_69986.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_69986.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_69986.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_69986.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____69990)::uu____69991 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____70004 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____70004 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____70040  -> dummy :: env1) env)
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
                                          let uu____70084 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____70084)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_70092 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_70092.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_70092.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____70093 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____70099  ->
                                 let uu____70100 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____70100);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_70115 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_70115.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_70115.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_70115.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_70115.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_70115.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_70115.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_70115.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_70115.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____70119)::uu____70120 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____70135 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____70135 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____70171  -> dummy :: env1) env)
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
                                          let uu____70215 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____70215)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_70223 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_70223.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_70223.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____70224 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____70230  ->
                                 let uu____70231 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____70231);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_70246 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_70246.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_70246.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_70246.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_70246.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_70246.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_70246.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_70246.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_70246.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____70250)::uu____70251 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____70266 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____70266 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____70302  -> dummy :: env1) env)
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
                                          let uu____70346 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____70346)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_70354 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_70354.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_70354.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____70355 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____70361  ->
                                 let uu____70362 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____70362);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_70377 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_70377.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_70377.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_70377.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_70377.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_70377.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_70377.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_70377.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_70377.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____70381)::uu____70382 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____70401 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____70401 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____70437  -> dummy :: env1) env)
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
                                          let uu____70481 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____70481)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_70489 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_70489.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_70489.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____70490 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____70496  ->
                                 let uu____70497 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____70497);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_70512 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_70512.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_70512.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_70512.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_70512.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_70512.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_70512.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_70512.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_70512.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____70520 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____70520 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____70556  -> dummy :: env1) env)
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
                                          let uu____70600 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____70600)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___2013_70608 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___2013_70608.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___2013_70608.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____70609 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____70615  ->
                                 let uu____70616 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____70616);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___2020_70631 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2020_70631.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___2020_70631.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2020_70631.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2020_70631.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2020_70631.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2020_70631.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2020_70631.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2020_70631.FStar_TypeChecker_Cfg.reifying)
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
                      (fun uu____70675  ->
                         fun stack1  ->
                           match uu____70675 with
                           | (a,aq) ->
                               let uu____70687 =
                                 let uu____70688 =
                                   let uu____70695 =
                                     let uu____70696 =
                                       let uu____70728 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____70728, false)  in
                                     Clos uu____70696  in
                                   (uu____70695, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____70688  in
                               uu____70687 :: stack1) args)
                  in
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____70796  ->
                     let uu____70797 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____70797);
                norm cfg env stack1 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,uu____70811) when
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
                             ((let uu___2047_70856 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2047_70856.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2047_70856.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____70857 ->
                      let uu____70872 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____70872)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____70876 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____70876 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____70907 =
                          let uu____70908 =
                            let uu____70915 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___2056_70921 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2056_70921.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___2056_70921.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____70915)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____70908  in
                        mk uu____70907 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____70945 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____70945
               else
                 (let uu____70948 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____70948 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____70956 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____70982  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____70956 c1  in
                      let t2 =
                        let uu____71006 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____71006 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____71119)::uu____71120 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____71133  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____71135)::uu____71136 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____71147  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____71149,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____71150;
                                   FStar_Syntax_Syntax.vars = uu____71151;_},uu____71152,uu____71153))::uu____71154
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____71161  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____71163)::uu____71164 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____71175  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____71177 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____71180  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____71185  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____71211 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____71211
                         | FStar_Util.Inr c ->
                             let uu____71225 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____71225
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____71248 =
                               let uu____71249 =
                                 let uu____71276 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____71276, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____71249
                                in
                             mk uu____71248 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____71311 ->
                           let uu____71312 =
                             let uu____71313 =
                               let uu____71314 =
                                 let uu____71341 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____71341, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____71314
                                in
                             mk uu____71313 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____71312))))
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
                   let uu___2135_71419 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___2137_71422 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___2137_71422.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___2135_71419.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___2135_71419.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___2135_71419.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___2135_71419.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___2135_71419.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___2135_71419.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___2135_71419.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___2135_71419.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____71463 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____71463 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___2150_71483 = cfg  in
                               let uu____71484 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___2150_71483.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____71484;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___2150_71483.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___2150_71483.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___2150_71483.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___2150_71483.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___2150_71483.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___2150_71483.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___2150_71483.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____71491 =
                                 let uu____71492 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____71492  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____71491
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___2157_71495 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___2157_71495.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2157_71495.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2157_71495.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2157_71495.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____71496 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____71496
           | FStar_Syntax_Syntax.Tm_let
               ((uu____71509,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____71510;
                               FStar_Syntax_Syntax.lbunivs = uu____71511;
                               FStar_Syntax_Syntax.lbtyp = uu____71512;
                               FStar_Syntax_Syntax.lbeff = uu____71513;
                               FStar_Syntax_Syntax.lbdef = uu____71514;
                               FStar_Syntax_Syntax.lbattrs = uu____71515;
                               FStar_Syntax_Syntax.lbpos = uu____71516;_}::uu____71517),uu____71518)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name
                   cfg.FStar_TypeChecker_Cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____71564 =
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
               if uu____71564
               then
                 let binder =
                   let uu____71568 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____71568  in
                 let env1 =
                   let uu____71578 =
                     let uu____71585 =
                       let uu____71586 =
                         let uu____71618 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____71618,
                           false)
                          in
                       Clos uu____71586  in
                     ((FStar_Pervasives_Native.Some binder), uu____71585)  in
                   uu____71578 :: env  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____71693  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                 then
                   (FStar_TypeChecker_Cfg.log cfg
                      (fun uu____71700  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____71702 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____71702))
                 else
                   (let uu____71705 =
                      let uu____71710 =
                        let uu____71711 =
                          let uu____71718 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____71718
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____71711]  in
                      FStar_Syntax_Subst.open_term uu____71710 body  in
                    match uu____71705 with
                    | (bs,body1) ->
                        (FStar_TypeChecker_Cfg.log cfg
                           (fun uu____71745  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____71754 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____71754  in
                            FStar_Util.Inl
                              (let uu___2199_71770 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2199_71770.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2199_71770.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____71773  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___2204_71776 = lb  in
                             let uu____71777 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___2204_71776.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___2204_71776.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____71777;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___2204_71776.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___2204_71776.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____71806  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___2211_71831 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps =
                                 (uu___2211_71831.FStar_TypeChecker_Cfg.steps);
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___2211_71831.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___2211_71831.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 (uu___2211_71831.FStar_TypeChecker_Cfg.delta_level);
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___2211_71831.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong = true;
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___2211_71831.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___2211_71831.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___2211_71831.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           FStar_TypeChecker_Cfg.log cfg1
                             (fun uu____71835  ->
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
               let uu____71856 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____71856 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____71892 =
                               let uu___2227_71893 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2227_71893.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2227_71893.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____71892  in
                           let uu____71894 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____71894 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____71920 =
                                   FStar_List.map (fun uu____71936  -> dummy)
                                     lbs1
                                    in
                                 let uu____71937 =
                                   let uu____71946 =
                                     FStar_List.map
                                       (fun uu____71968  -> dummy) xs1
                                      in
                                   FStar_List.append uu____71946 env  in
                                 FStar_List.append uu____71920 uu____71937
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____71994 =
                                       let uu___2241_71995 = rc  in
                                       let uu____71996 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___2241_71995.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____71996;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___2241_71995.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____71994
                                 | uu____72005 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___2246_72011 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___2246_72011.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___2246_72011.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___2246_72011.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___2246_72011.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____72021 =
                        FStar_List.map (fun uu____72037  -> dummy) lbs2  in
                      FStar_List.append uu____72021 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____72045 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____72045 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___2255_72061 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___2255_72061.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___2255_72061.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
               ->
               let uu____72095 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____72095
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____72116 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____72194  ->
                        match uu____72194 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___2271_72319 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2271_72319.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___2271_72319.FStar_Syntax_Syntax.sort)
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
               (match uu____72116 with
                | (rec_env,memos,uu____72510) ->
                    let uu____72565 =
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
                             let uu____72814 =
                               let uu____72821 =
                                 let uu____72822 =
                                   let uu____72854 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____72854, false)
                                    in
                                 Clos uu____72822  in
                               (FStar_Pervasives_Native.None, uu____72821)
                                in
                             uu____72814 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____72939  ->
                     let uu____72940 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____72940);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____72964 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____72968::uu____72969 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____72974) ->
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
                             | uu____73005 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern args ->
                                  let uu____73021 =
                                    norm_pattern_args cfg env args  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____73021
                              | uu____73034 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____73040 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____73064 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____73078 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____73092 =
                        let uu____73094 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____73096 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____73094 uu____73096
                         in
                      failwith uu____73092
                    else
                      (let uu____73101 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____73101)
                | uu____73102 -> norm cfg env stack t2))

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
              let uu____73111 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____73111 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____73125  ->
                        let uu____73126 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____73126);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____73139  ->
                        let uu____73140 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____73142 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____73140 uu____73142);
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
                      | (UnivArgs (us',uu____73155))::stack1 ->
                          ((let uu____73164 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____73164
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____73172 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____73172) us'
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
                      | uu____73208 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____73211 ->
                          let uu____73214 =
                            let uu____73216 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____73216
                             in
                          failwith uu____73214
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
                  let uu___2377_73244 = cfg  in
                  let uu____73245 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____73245;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___2377_73244.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___2377_73244.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___2377_73244.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___2377_73244.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___2377_73244.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___2377_73244.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___2377_73244.FStar_TypeChecker_Cfg.reifying)
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
                     (uu____73276,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____73277;
                                    FStar_Syntax_Syntax.vars = uu____73278;_},uu____73279,uu____73280))::uu____73281
                     -> ()
                 | uu____73286 ->
                     let uu____73289 =
                       let uu____73291 = stack_to_string stack  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____73291
                        in
                     failwith uu____73289);
                (let head0 = head1  in
                 let head2 = FStar_Syntax_Util.unascribe head1  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____73300  ->
                      let uu____73301 = FStar_Syntax_Print.tag_of_term head2
                         in
                      let uu____73303 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____73301
                        uu____73303);
                 (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                  let uu____73307 =
                    let uu____73308 = FStar_Syntax_Subst.compress head3  in
                    uu____73308.FStar_Syntax_Syntax.n  in
                  match uu____73307 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let ed =
                        let uu____73329 =
                          FStar_TypeChecker_Env.norm_eff_name
                            cfg.FStar_TypeChecker_Cfg.tcenv m
                           in
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv uu____73329
                         in
                      let uu____73330 = ed.FStar_Syntax_Syntax.bind_repr  in
                      (match uu____73330 with
                       | (uu____73331,bind_repr) ->
                           (match lb.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____73341 ->
                                failwith
                                  "Cannot reify a top-level let binding"
                            | FStar_Util.Inl x ->
                                let is_return e =
                                  let uu____73352 =
                                    let uu____73353 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____73353.FStar_Syntax_Syntax.n  in
                                  match uu____73352 with
                                  | FStar_Syntax_Syntax.Tm_meta
                                      (e1,FStar_Syntax_Syntax.Meta_monadic
                                       (uu____73359,uu____73360))
                                      ->
                                      let uu____73369 =
                                        let uu____73370 =
                                          FStar_Syntax_Subst.compress e1  in
                                        uu____73370.FStar_Syntax_Syntax.n  in
                                      (match uu____73369 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                            (uu____73376,msrc,uu____73378))
                                           when
                                           FStar_Syntax_Util.is_pure_effect
                                             msrc
                                           ->
                                           let uu____73387 =
                                             FStar_Syntax_Subst.compress e2
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____73387
                                       | uu____73388 ->
                                           FStar_Pervasives_Native.None)
                                  | uu____73389 ->
                                      FStar_Pervasives_Native.None
                                   in
                                let uu____73390 =
                                  is_return lb.FStar_Syntax_Syntax.lbdef  in
                                (match uu____73390 with
                                 | FStar_Pervasives_Native.Some e ->
                                     let lb1 =
                                       let uu___2449_73395 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___2449_73395.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___2449_73395.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           (uu___2449_73395.FStar_Syntax_Syntax.lbtyp);
                                         FStar_Syntax_Syntax.lbeff =
                                           FStar_Parser_Const.effect_PURE_lid;
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___2449_73395.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___2449_73395.FStar_Syntax_Syntax.lbpos)
                                       }  in
                                     let uu____73396 = FStar_List.tl stack
                                        in
                                     let uu____73397 =
                                       let uu____73398 =
                                         let uu____73405 =
                                           let uu____73406 =
                                             let uu____73420 =
                                               FStar_Syntax_Util.mk_reify
                                                 body
                                                in
                                             ((false, [lb1]), uu____73420)
                                              in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____73406
                                            in
                                         FStar_Syntax_Syntax.mk uu____73405
                                          in
                                       uu____73398
                                         FStar_Pervasives_Native.None
                                         head3.FStar_Syntax_Syntax.pos
                                        in
                                     norm cfg env uu____73396 uu____73397
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____73436 =
                                       let uu____73438 = is_return body  in
                                       match uu____73438 with
                                       | FStar_Pervasives_Native.Some
                                           {
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_bvar y;
                                             FStar_Syntax_Syntax.pos =
                                               uu____73443;
                                             FStar_Syntax_Syntax.vars =
                                               uu____73444;_}
                                           -> FStar_Syntax_Syntax.bv_eq x y
                                       | uu____73447 -> false  in
                                     if uu____73436
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
                                          let uu____73471 =
                                            let uu____73478 =
                                              let uu____73479 =
                                                let uu____73498 =
                                                  let uu____73507 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____73507]  in
                                                (uu____73498, body1,
                                                  (FStar_Pervasives_Native.Some
                                                     body_rc))
                                                 in
                                              FStar_Syntax_Syntax.Tm_abs
                                                uu____73479
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____73478
                                             in
                                          uu____73471
                                            FStar_Pervasives_Native.None
                                            body1.FStar_Syntax_Syntax.pos
                                           in
                                        let close1 = closure_as_term cfg env
                                           in
                                        let bind_inst =
                                          let uu____73546 =
                                            let uu____73547 =
                                              FStar_Syntax_Subst.compress
                                                bind_repr
                                               in
                                            uu____73547.FStar_Syntax_Syntax.n
                                             in
                                          match uu____73546 with
                                          | FStar_Syntax_Syntax.Tm_uinst
                                              (bind1,uu____73553::uu____73554::[])
                                              ->
                                              let uu____73559 =
                                                let uu____73566 =
                                                  let uu____73567 =
                                                    let uu____73574 =
                                                      let uu____73575 =
                                                        let uu____73576 =
                                                          close1
                                                            lb.FStar_Syntax_Syntax.lbtyp
                                                           in
                                                        (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.FStar_TypeChecker_Cfg.tcenv
                                                          uu____73576
                                                         in
                                                      let uu____73577 =
                                                        let uu____73580 =
                                                          let uu____73581 =
                                                            close1 t  in
                                                          (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                            cfg.FStar_TypeChecker_Cfg.tcenv
                                                            uu____73581
                                                           in
                                                        [uu____73580]  in
                                                      uu____73575 ::
                                                        uu____73577
                                                       in
                                                    (bind1, uu____73574)  in
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                    uu____73567
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____73566
                                                 in
                                              uu____73559
                                                FStar_Pervasives_Native.None
                                                rng
                                          | uu____73584 ->
                                              failwith
                                                "NIY : Reification of indexed effects"
                                           in
                                        let maybe_range_arg =
                                          let uu____73599 =
                                            FStar_Util.for_some
                                              (FStar_Syntax_Util.attr_eq
                                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                                              ed.FStar_Syntax_Syntax.eff_attrs
                                             in
                                          if uu____73599
                                          then
                                            let uu____73612 =
                                              let uu____73621 =
                                                FStar_TypeChecker_Cfg.embed_simple
                                                  FStar_Syntax_Embeddings.e_range
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____73621
                                               in
                                            let uu____73622 =
                                              let uu____73633 =
                                                let uu____73642 =
                                                  FStar_TypeChecker_Cfg.embed_simple
                                                    FStar_Syntax_Embeddings.e_range
                                                    body2.FStar_Syntax_Syntax.pos
                                                    body2.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Syntax_Syntax.as_arg
                                                  uu____73642
                                                 in
                                              [uu____73633]  in
                                            uu____73612 :: uu____73622
                                          else []  in
                                        let reified =
                                          let uu____73680 =
                                            let uu____73687 =
                                              let uu____73688 =
                                                let uu____73705 =
                                                  let uu____73716 =
                                                    let uu____73727 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        lb.FStar_Syntax_Syntax.lbtyp
                                                       in
                                                    let uu____73736 =
                                                      let uu____73747 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          t
                                                         in
                                                      [uu____73747]  in
                                                    uu____73727 ::
                                                      uu____73736
                                                     in
                                                  let uu____73780 =
                                                    let uu____73791 =
                                                      let uu____73802 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          FStar_Syntax_Syntax.tun
                                                         in
                                                      let uu____73811 =
                                                        let uu____73822 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            head4
                                                           in
                                                        let uu____73831 =
                                                          let uu____73842 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          let uu____73851 =
                                                            let uu____73862 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                body2
                                                               in
                                                            [uu____73862]  in
                                                          uu____73842 ::
                                                            uu____73851
                                                           in
                                                        uu____73822 ::
                                                          uu____73831
                                                         in
                                                      uu____73802 ::
                                                        uu____73811
                                                       in
                                                    FStar_List.append
                                                      maybe_range_arg
                                                      uu____73791
                                                     in
                                                  FStar_List.append
                                                    uu____73716 uu____73780
                                                   in
                                                (bind_inst, uu____73705)  in
                                              FStar_Syntax_Syntax.Tm_app
                                                uu____73688
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____73687
                                             in
                                          uu____73680
                                            FStar_Pervasives_Native.None rng
                                           in
                                        FStar_TypeChecker_Cfg.log cfg
                                          (fun uu____73943  ->
                                             let uu____73944 =
                                               FStar_Syntax_Print.term_to_string
                                                 head0
                                                in
                                             let uu____73946 =
                                               FStar_Syntax_Print.term_to_string
                                                 reified
                                                in
                                             FStar_Util.print2
                                               "Reified (1) <%s> to %s\n"
                                               uu____73944 uu____73946);
                                        (let uu____73949 =
                                           FStar_List.tl stack  in
                                         norm cfg env uu____73949 reified)))))
                  | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                      ((let uu____73977 = FStar_Options.defensive ()  in
                        if uu____73977
                        then
                          let is_arg_impure uu____73992 =
                            match uu____73992 with
                            | (e,q) ->
                                let uu____74006 =
                                  let uu____74007 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____74007.FStar_Syntax_Syntax.n  in
                                (match uu____74006 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____74023 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____74023
                                 | uu____74025 -> false)
                             in
                          let uu____74027 =
                            let uu____74029 =
                              let uu____74040 =
                                FStar_Syntax_Syntax.as_arg head_app  in
                              uu____74040 :: args  in
                            FStar_Util.for_some is_arg_impure uu____74029  in
                          (if uu____74027
                           then
                             let uu____74066 =
                               let uu____74072 =
                                 let uu____74074 =
                                   FStar_Syntax_Print.term_to_string head3
                                    in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____74074
                                  in
                               (FStar_Errors.Warning_Defensive, uu____74072)
                                in
                             FStar_Errors.log_issue
                               head3.FStar_Syntax_Syntax.pos uu____74066
                           else ())
                        else ());
                       (let fallback1 uu____74087 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____74091  ->
                               let uu____74092 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____74092 "");
                          (let uu____74096 = FStar_List.tl stack  in
                           let uu____74097 = FStar_Syntax_Util.mk_reify head3
                              in
                           norm cfg env uu____74096 uu____74097)
                           in
                        let fallback2 uu____74103 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____74107  ->
                               let uu____74108 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____74108 "");
                          (let uu____74112 = FStar_List.tl stack  in
                           let uu____74113 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (head3,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               head0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env uu____74112 uu____74113)
                           in
                        let uu____74118 =
                          let uu____74119 =
                            FStar_Syntax_Util.un_uinst head_app  in
                          uu____74119.FStar_Syntax_Syntax.n  in
                        match uu____74118 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____74125 =
                              let uu____74127 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____74127  in
                            if uu____74125
                            then fallback1 ()
                            else
                              (let uu____74132 =
                                 let uu____74134 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____74134  in
                               if uu____74132
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____74151 =
                                      let uu____74156 =
                                        FStar_Syntax_Util.mk_reify head_app
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____74156 args
                                       in
                                    uu____74151 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____74157 = FStar_List.tl stack  in
                                  norm cfg env uu____74157 t1))
                        | uu____74158 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____74160) ->
                      do_reify_monadic fallback cfg env stack e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____74184 = closure_as_term cfg env t'  in
                        reify_lift cfg e msrc mtgt uu____74184  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____74188  ->
                            let uu____74189 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____74189);
                       (let uu____74192 = FStar_List.tl stack  in
                        norm cfg env uu____74192 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                      let branches1 =
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun uu____74313  ->
                                match uu____74313 with
                                | (pat,wopt,tm) ->
                                    let uu____74361 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____74361)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                          head3.FStar_Syntax_Syntax.pos
                         in
                      let uu____74393 = FStar_List.tl stack  in
                      norm cfg env uu____74393 tm
                  | uu____74394 -> fallback ()))

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
              (fun uu____74408  ->
                 let uu____74409 = FStar_Ident.string_of_lid msrc  in
                 let uu____74411 = FStar_Ident.string_of_lid mtgt  in
                 let uu____74413 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____74409
                   uu____74411 uu____74413);
            (let uu____74416 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____74416
             then
               let ed =
                 let uu____74420 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____74420  in
               let uu____74421 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____74421 with
               | (uu____74422,return_repr) ->
                   let return_inst =
                     let uu____74435 =
                       let uu____74436 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____74436.FStar_Syntax_Syntax.n  in
                     match uu____74435 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____74442::[]) ->
                         let uu____74447 =
                           let uu____74454 =
                             let uu____74455 =
                               let uu____74462 =
                                 let uu____74463 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____74463]  in
                               (return_tm, uu____74462)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____74455  in
                           FStar_Syntax_Syntax.mk uu____74454  in
                         uu____74447 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____74466 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____74470 =
                     let uu____74477 =
                       let uu____74478 =
                         let uu____74495 =
                           let uu____74506 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____74515 =
                             let uu____74526 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____74526]  in
                           uu____74506 :: uu____74515  in
                         (return_inst, uu____74495)  in
                       FStar_Syntax_Syntax.Tm_app uu____74478  in
                     FStar_Syntax_Syntax.mk uu____74477  in
                   uu____74470 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____74573 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____74573 with
                | FStar_Pervasives_Native.None  ->
                    let uu____74576 =
                      let uu____74578 = FStar_Ident.text_of_lid msrc  in
                      let uu____74580 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____74578 uu____74580
                       in
                    failwith uu____74576
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____74583;
                      FStar_TypeChecker_Env.mtarget = uu____74584;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____74585;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____74607 =
                      let uu____74609 = FStar_Ident.text_of_lid msrc  in
                      let uu____74611 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____74609 uu____74611
                       in
                    failwith uu____74607
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____74614;
                      FStar_TypeChecker_Env.mtarget = uu____74615;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____74616;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____74651 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____74652 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____74651 t FStar_Syntax_Syntax.tun uu____74652))

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
                (fun uu____74722  ->
                   match uu____74722 with
                   | (a,imp) ->
                       let uu____74741 = norm cfg env [] a  in
                       (uu____74741, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____74751  ->
             let uu____74752 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____74754 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____74752 uu____74754);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____74780 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _74783  -> FStar_Pervasives_Native.Some _74783)
                     uu____74780
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2599_74784 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2599_74784.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2599_74784.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____74806 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _74809  -> FStar_Pervasives_Native.Some _74809)
                     uu____74806
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2610_74810 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2610_74810.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2610_74810.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____74855  ->
                      match uu____74855 with
                      | (a,i) ->
                          let uu____74875 = norm cfg env [] a  in
                          (uu____74875, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___600_74897  ->
                       match uu___600_74897 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____74901 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____74901
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___2627_74909 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2629_74912 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2629_74912.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2627_74909.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2627_74909.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun b  ->
        let uu____74916 = b  in
        match uu____74916 with
        | (x,imp) ->
            let x1 =
              let uu___2637_74924 = x  in
              let uu____74925 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2637_74924.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2637_74924.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____74925
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____74936 =
                    let uu____74937 = closure_as_term cfg env t  in
                    FStar_Syntax_Syntax.Meta uu____74937  in
                  FStar_Pervasives_Native.Some uu____74936
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____74948 =
          FStar_List.fold_left
            (fun uu____74982  ->
               fun b  ->
                 match uu____74982 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____74948 with | (nbs,uu____75062) -> FStar_List.rev nbs

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
            let uu____75094 =
              let uu___2662_75095 = rc  in
              let uu____75096 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2662_75095.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____75096;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2662_75095.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____75094
        | uu____75105 -> lopt

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
            (let uu____75115 = FStar_Syntax_Print.term_to_string tm  in
             let uu____75117 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____75115 uu____75117)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___601_75129  ->
      match uu___601_75129 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____75142 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____75142 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____75146 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____75146)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____75154 = norm_cb cfg  in
            reduce_primops uu____75154 cfg env tm  in
          let uu____75159 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____75159
          then tm1
          else
            (let w t =
               let uu___2690_75178 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2690_75178.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2690_75178.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____75190 =
                 let uu____75191 = FStar_Syntax_Util.unmeta t  in
                 uu____75191.FStar_Syntax_Syntax.n  in
               match uu____75190 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____75203 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____75267)::args1,(bv,uu____75270)::bs1) ->
                   let uu____75324 =
                     let uu____75325 = FStar_Syntax_Subst.compress t  in
                     uu____75325.FStar_Syntax_Syntax.n  in
                   (match uu____75324 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____75330 -> false)
               | ([],[]) -> true
               | (uu____75361,uu____75362) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____75413 = FStar_Syntax_Print.term_to_string t  in
                  let uu____75415 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____75413
                    uu____75415)
               else ();
               (let uu____75420 = FStar_Syntax_Util.head_and_args' t  in
                match uu____75420 with
                | (hd1,args) ->
                    let uu____75459 =
                      let uu____75460 = FStar_Syntax_Subst.compress hd1  in
                      uu____75460.FStar_Syntax_Syntax.n  in
                    (match uu____75459 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____75468 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____75470 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____75472 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____75468 uu____75470 uu____75472)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____75477 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____75495 = FStar_Syntax_Print.term_to_string t  in
                  let uu____75497 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____75495
                    uu____75497)
               else ();
               (let uu____75502 = FStar_Syntax_Util.is_squash t  in
                match uu____75502 with
                | FStar_Pervasives_Native.Some (uu____75513,t') ->
                    is_applied bs t'
                | uu____75525 ->
                    let uu____75534 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____75534 with
                     | FStar_Pervasives_Native.Some (uu____75545,t') ->
                         is_applied bs t'
                     | uu____75557 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____75581 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____75581 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____75588)::(q,uu____75590)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____75633 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____75635 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____75633 uu____75635)
                    else ();
                    (let uu____75640 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____75640 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____75645 =
                           let uu____75646 = FStar_Syntax_Subst.compress p
                              in
                           uu____75646.FStar_Syntax_Syntax.n  in
                         (match uu____75645 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____75657 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____75657))
                          | uu____75660 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____75663)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____75688 =
                           let uu____75689 = FStar_Syntax_Subst.compress p1
                              in
                           uu____75689.FStar_Syntax_Syntax.n  in
                         (match uu____75688 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____75700 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____75700))
                          | uu____75703 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____75707 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____75707 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____75712 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____75712 with
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
                                     let uu____75726 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____75726))
                               | uu____75729 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____75734)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____75759 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____75759 with
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
                                     let uu____75773 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____75773))
                               | uu____75776 -> FStar_Pervasives_Native.None)
                          | uu____75779 -> FStar_Pervasives_Native.None)
                     | uu____75782 -> FStar_Pervasives_Native.None))
               | uu____75785 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____75798 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____75798 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____75804)::[],uu____75805,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____75825 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____75827 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____75825
                         uu____75827)
                    else ();
                    is_quantified_const bv phi')
               | uu____75832 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____75847 =
                 let uu____75848 = FStar_Syntax_Subst.compress phi  in
                 uu____75848.FStar_Syntax_Syntax.n  in
               match uu____75847 with
               | FStar_Syntax_Syntax.Tm_match (uu____75854,br::brs) ->
                   let uu____75921 = br  in
                   (match uu____75921 with
                    | (uu____75939,uu____75940,e) ->
                        let r =
                          let uu____75962 = simp_t e  in
                          match uu____75962 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____75974 =
                                FStar_List.for_all
                                  (fun uu____75993  ->
                                     match uu____75993 with
                                     | (uu____76007,uu____76008,e') ->
                                         let uu____76022 = simp_t e'  in
                                         uu____76022 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____75974
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____76038 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____76048 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____76048
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____76086 =
                 match uu____76086 with
                 | (t1,q) ->
                     let uu____76107 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____76107 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____76139 -> (t1, q))
                  in
               let uu____76152 = FStar_Syntax_Util.head_and_args t  in
               match uu____76152 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____76232 =
                 let uu____76233 = FStar_Syntax_Util.unmeta ty  in
                 uu____76233.FStar_Syntax_Syntax.n  in
               match uu____76232 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____76238) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____76243,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____76267 -> false  in
             let simplify1 arg =
               let uu____76300 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____76300, arg)  in
             let uu____76315 = is_forall_const tm1  in
             match uu____76315 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____76321 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____76323 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____76321
                       uu____76323)
                  else ();
                  (let uu____76328 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____76328))
             | FStar_Pervasives_Native.None  ->
                 let uu____76329 =
                   let uu____76330 = FStar_Syntax_Subst.compress tm1  in
                   uu____76330.FStar_Syntax_Syntax.n  in
                 (match uu____76329 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____76334;
                              FStar_Syntax_Syntax.vars = uu____76335;_},uu____76336);
                         FStar_Syntax_Syntax.pos = uu____76337;
                         FStar_Syntax_Syntax.vars = uu____76338;_},args)
                      ->
                      let uu____76368 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____76368
                      then
                        let uu____76371 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____76371 with
                         | (FStar_Pervasives_Native.Some (true ),uu____76429)::
                             (uu____76430,(arg,uu____76432))::[] ->
                             maybe_auto_squash arg
                         | (uu____76505,(arg,uu____76507))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____76508)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____76581)::uu____76582::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____76652::(FStar_Pervasives_Native.Some (false
                                         ),uu____76653)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____76723 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____76741 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____76741
                         then
                           let uu____76744 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____76744 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____76802)::uu____76803::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____76873::(FStar_Pervasives_Native.Some (true
                                           ),uu____76874)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____76944)::(uu____76945,(arg,uu____76947))::[]
                               -> maybe_auto_squash arg
                           | (uu____77020,(arg,uu____77022))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____77023)::[]
                               -> maybe_auto_squash arg
                           | uu____77096 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____77114 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____77114
                            then
                              let uu____77117 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____77117 with
                              | uu____77175::(FStar_Pervasives_Native.Some
                                              (true ),uu____77176)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____77246)::uu____77247::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____77317)::(uu____77318,(arg,uu____77320))::[]
                                  -> maybe_auto_squash arg
                              | (uu____77393,(p,uu____77395))::(uu____77396,
                                                                (q,uu____77398))::[]
                                  ->
                                  let uu____77470 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____77470
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____77475 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____77493 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____77493
                               then
                                 let uu____77496 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____77496 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____77554)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____77555)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____77629)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____77630)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____77704)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____77705)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____77779)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____77780)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____77854,(arg,uu____77856))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____77857)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____77930)::(uu____77931,(arg,uu____77933))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____78006,(arg,uu____78008))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____78009)::[]
                                     ->
                                     let uu____78082 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____78082
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____78083)::(uu____78084,(arg,uu____78086))::[]
                                     ->
                                     let uu____78159 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____78159
                                 | (uu____78160,(p,uu____78162))::(uu____78163,
                                                                   (q,uu____78165))::[]
                                     ->
                                     let uu____78237 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____78237
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____78242 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____78260 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____78260
                                  then
                                    let uu____78263 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____78263 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____78321)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____78365)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____78409 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____78427 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____78427
                                     then
                                       match args with
                                       | (t,uu____78431)::[] ->
                                           let uu____78456 =
                                             let uu____78457 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____78457.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____78456 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____78460::[],body,uu____78462)
                                                ->
                                                let uu____78497 = simp_t body
                                                   in
                                                (match uu____78497 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____78503 -> tm1)
                                            | uu____78507 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____78509))::(t,uu____78511)::[]
                                           ->
                                           let uu____78551 =
                                             let uu____78552 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____78552.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____78551 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____78555::[],body,uu____78557)
                                                ->
                                                let uu____78592 = simp_t body
                                                   in
                                                (match uu____78592 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____78600 -> tm1)
                                            | uu____78604 -> tm1)
                                       | uu____78605 -> tm1
                                     else
                                       (let uu____78618 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____78618
                                        then
                                          match args with
                                          | (t,uu____78622)::[] ->
                                              let uu____78647 =
                                                let uu____78648 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____78648.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____78647 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____78651::[],body,uu____78653)
                                                   ->
                                                   let uu____78688 =
                                                     simp_t body  in
                                                   (match uu____78688 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____78694 -> tm1)
                                               | uu____78698 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____78700))::(t,uu____78702)::[]
                                              ->
                                              let uu____78742 =
                                                let uu____78743 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____78743.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____78742 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____78746::[],body,uu____78748)
                                                   ->
                                                   let uu____78783 =
                                                     simp_t body  in
                                                   (match uu____78783 with
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
                                                    | uu____78791 -> tm1)
                                               | uu____78795 -> tm1)
                                          | uu____78796 -> tm1
                                        else
                                          (let uu____78809 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____78809
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____78812;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____78813;_},uu____78814)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____78840;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____78841;_},uu____78842)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____78868 -> tm1
                                           else
                                             (let uu____78881 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____78881
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____78895 =
                                                    let uu____78896 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____78896.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____78895 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____78907 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     (Prims.parse_int "1")
                                                 then
                                                   let t =
                                                     let uu____78921 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____78921
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____78960 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____78960
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____78966 =
                                                         let uu____78967 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____78967.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____78966 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____78970 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____78978 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____78978
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____78987
                                                                  =
                                                                  let uu____78988
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____78988.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____78987
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____78994)
                                                                    -> hd1
                                                                | uu____79019
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____79023
                                                                =
                                                                let uu____79034
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____79034]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____79023)
                                                       | uu____79067 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____79072 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____79072 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____79092 ->
                                                     let uu____79101 =
                                                       let uu____79108 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____79108 cfg env
                                                        in
                                                     uu____79101 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____79114;
                         FStar_Syntax_Syntax.vars = uu____79115;_},args)
                      ->
                      let uu____79141 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____79141
                      then
                        let uu____79144 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____79144 with
                         | (FStar_Pervasives_Native.Some (true ),uu____79202)::
                             (uu____79203,(arg,uu____79205))::[] ->
                             maybe_auto_squash arg
                         | (uu____79278,(arg,uu____79280))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____79281)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____79354)::uu____79355::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____79425::(FStar_Pervasives_Native.Some (false
                                         ),uu____79426)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____79496 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____79514 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____79514
                         then
                           let uu____79517 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____79517 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____79575)::uu____79576::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____79646::(FStar_Pervasives_Native.Some (true
                                           ),uu____79647)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____79717)::(uu____79718,(arg,uu____79720))::[]
                               -> maybe_auto_squash arg
                           | (uu____79793,(arg,uu____79795))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____79796)::[]
                               -> maybe_auto_squash arg
                           | uu____79869 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____79887 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____79887
                            then
                              let uu____79890 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____79890 with
                              | uu____79948::(FStar_Pervasives_Native.Some
                                              (true ),uu____79949)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____80019)::uu____80020::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____80090)::(uu____80091,(arg,uu____80093))::[]
                                  -> maybe_auto_squash arg
                              | (uu____80166,(p,uu____80168))::(uu____80169,
                                                                (q,uu____80171))::[]
                                  ->
                                  let uu____80243 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____80243
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____80248 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____80266 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____80266
                               then
                                 let uu____80269 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____80269 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____80327)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____80328)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____80402)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____80403)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____80477)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____80478)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____80552)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____80553)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____80627,(arg,uu____80629))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____80630)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____80703)::(uu____80704,(arg,uu____80706))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____80779,(arg,uu____80781))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____80782)::[]
                                     ->
                                     let uu____80855 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____80855
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____80856)::(uu____80857,(arg,uu____80859))::[]
                                     ->
                                     let uu____80932 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____80932
                                 | (uu____80933,(p,uu____80935))::(uu____80936,
                                                                   (q,uu____80938))::[]
                                     ->
                                     let uu____81010 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____81010
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____81015 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____81033 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____81033
                                  then
                                    let uu____81036 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____81036 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____81094)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____81138)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____81182 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____81200 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____81200
                                     then
                                       match args with
                                       | (t,uu____81204)::[] ->
                                           let uu____81229 =
                                             let uu____81230 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____81230.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____81229 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____81233::[],body,uu____81235)
                                                ->
                                                let uu____81270 = simp_t body
                                                   in
                                                (match uu____81270 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____81276 -> tm1)
                                            | uu____81280 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____81282))::(t,uu____81284)::[]
                                           ->
                                           let uu____81324 =
                                             let uu____81325 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____81325.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____81324 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____81328::[],body,uu____81330)
                                                ->
                                                let uu____81365 = simp_t body
                                                   in
                                                (match uu____81365 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____81373 -> tm1)
                                            | uu____81377 -> tm1)
                                       | uu____81378 -> tm1
                                     else
                                       (let uu____81391 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____81391
                                        then
                                          match args with
                                          | (t,uu____81395)::[] ->
                                              let uu____81420 =
                                                let uu____81421 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____81421.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____81420 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____81424::[],body,uu____81426)
                                                   ->
                                                   let uu____81461 =
                                                     simp_t body  in
                                                   (match uu____81461 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____81467 -> tm1)
                                               | uu____81471 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____81473))::(t,uu____81475)::[]
                                              ->
                                              let uu____81515 =
                                                let uu____81516 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____81516.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____81515 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____81519::[],body,uu____81521)
                                                   ->
                                                   let uu____81556 =
                                                     simp_t body  in
                                                   (match uu____81556 with
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
                                                    | uu____81564 -> tm1)
                                               | uu____81568 -> tm1)
                                          | uu____81569 -> tm1
                                        else
                                          (let uu____81582 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____81582
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____81585;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____81586;_},uu____81587)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____81613;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____81614;_},uu____81615)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____81641 -> tm1
                                           else
                                             (let uu____81654 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____81654
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____81668 =
                                                    let uu____81669 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____81669.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____81668 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____81680 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     (Prims.parse_int "1")
                                                 then
                                                   let t =
                                                     let uu____81694 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____81694
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____81729 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____81729
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____81735 =
                                                         let uu____81736 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____81736.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____81735 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____81739 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____81747 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____81747
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____81756
                                                                  =
                                                                  let uu____81757
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____81757.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____81756
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____81763)
                                                                    -> hd1
                                                                | uu____81788
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____81792
                                                                =
                                                                let uu____81803
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____81803]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____81792)
                                                       | uu____81836 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____81841 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____81841 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____81861 ->
                                                     let uu____81870 =
                                                       let uu____81877 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____81877 cfg env
                                                        in
                                                     uu____81870 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____81888 = simp_t t  in
                      (match uu____81888 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____81897 ->
                      let uu____81920 = is_const_match tm1  in
                      (match uu____81920 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____81929 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____81939  ->
               (let uu____81941 = FStar_Syntax_Print.tag_of_term t  in
                let uu____81943 = FStar_Syntax_Print.term_to_string t  in
                let uu____81945 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____81953 =
                  let uu____81955 =
                    let uu____81958 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____81958
                     in
                  stack_to_string uu____81955  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____81941 uu____81943 uu____81945 uu____81953);
               (let uu____81983 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____81983
                then
                  let uu____81987 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____81987 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____81994 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____81996 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____81998 =
                          let uu____82000 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____82000
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____81994
                          uu____81996 uu____81998);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____82022 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack with
                | (Arg uu____82030)::uu____82031 -> true
                | uu____82041 -> false)
              in
           if uu____82022
           then
             let uu____82044 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____82044 (norm cfg env stack)
           else
             (let t1 = maybe_simplify cfg env stack t  in
              match stack with
              | [] -> t1
              | (Debug (tm,time_then))::stack1 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now ()  in
                      let uu____82058 =
                        let uu____82060 =
                          let uu____82062 =
                            FStar_Util.time_diff time_then time_now  in
                          FStar_Pervasives_Native.snd uu____82062  in
                        FStar_Util.string_of_int uu____82060  in
                      let uu____82069 = FStar_Syntax_Print.term_to_string tm
                         in
                      let uu____82071 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print3
                        "Normalized term (%s ms) %s\n\tto term %s\n"
                        uu____82058 uu____82069 uu____82071)
                   else ();
                   rebuild cfg env stack1 t1)
              | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
              | (Meta (uu____82080,m,r))::stack1 ->
                  let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
                  rebuild cfg env stack1 t2
              | (MemoLazy r)::stack1 ->
                  (set_memo cfg r (env, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu____82109  ->
                        let uu____82110 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 "\tSet memo %s\n" uu____82110);
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
                  let uu____82153 =
                    let uu___3319_82154 = FStar_Syntax_Util.abs bs1 t1 lopt1
                       in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___3319_82154.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___3319_82154.FStar_Syntax_Syntax.vars)
                    }  in
                  rebuild cfg env stack1 uu____82153
              | (Arg (Univ uu____82157,uu____82158,uu____82159))::uu____82160
                  -> failwith "Impossible"
              | (Arg (Dummy ,uu____82164,uu____82165))::uu____82166 ->
                  failwith "Impossible"
              | (UnivArgs (us,r))::stack1 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                  rebuild cfg env stack1 t2
              | (Arg
                  (Clos (env_arg,tm,uu____82182,uu____82183),aq,r))::stack1
                  when
                  let uu____82235 = head_of t1  in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____82235 ->
                  let t2 =
                    let uu____82239 =
                      let uu____82244 =
                        let uu____82245 = closure_as_term cfg env_arg tm  in
                        (uu____82245, aq)  in
                      FStar_Syntax_Syntax.extend_app t1 uu____82244  in
                    uu____82239 FStar_Pervasives_Native.None r  in
                  rebuild cfg env stack1 t2
              | (Arg (Clos (env_arg,tm,m,uu____82255),aq,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____82310  ->
                        let uu____82311 =
                          FStar_Syntax_Print.term_to_string tm  in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____82311);
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
                     (let uu____82331 = FStar_ST.op_Bang m  in
                      match uu____82331 with
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
                      | FStar_Pervasives_Native.Some (uu____82419,a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq)
                              FStar_Pervasives_Native.None r
                             in
                          rebuild cfg env_arg stack1 t2))
              | (App (env1,head1,aq,r))::stack' when should_reify cfg stack
                  ->
                  let t0 = t1  in
                  let fallback msg uu____82475 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____82480  ->
                         let uu____82481 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____82481);
                    (let t2 =
                       FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env1 stack' t2)
                     in
                  let uu____82491 =
                    let uu____82492 = FStar_Syntax_Subst.compress t1  in
                    uu____82492.FStar_Syntax_Syntax.n  in
                  (match uu____82491 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env1 stack t2 m
                         ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc,mtgt,ty))
                       ->
                       let lifted =
                         let uu____82520 = closure_as_term cfg env1 ty  in
                         reify_lift cfg t2 msrc mtgt uu____82520  in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____82524  ->
                             let uu____82525 =
                               FStar_Syntax_Print.term_to_string lifted  in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____82525);
                        (let uu____82528 = FStar_List.tl stack  in
                         norm cfg env1 uu____82528 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu____82529);
                          FStar_Syntax_Syntax.pos = uu____82530;
                          FStar_Syntax_Syntax.vars = uu____82531;_},(e,uu____82533)::[])
                       -> norm cfg env1 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____82572 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____82589 = FStar_Syntax_Util.head_and_args t1
                          in
                       (match uu____82589 with
                        | (hd1,args) ->
                            let uu____82632 =
                              let uu____82633 =
                                FStar_Syntax_Util.un_uinst hd1  in
                              uu____82633.FStar_Syntax_Syntax.n  in
                            (match uu____82632 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____82637 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv
                                    in
                                 (match uu____82637 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____82640;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____82641;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____82642;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n1;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____82644;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____82645;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____82646;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____82647;_}
                                      when (FStar_List.length args) = n1 ->
                                      norm cfg env1 stack' t1
                                  | uu____82683 -> fallback " (3)" ())
                             | uu____82687 -> fallback " (4)" ()))
                   | uu____82689 -> fallback " (2)" ())
              | (App (env1,head1,aq,r))::stack1 ->
                  let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack1 t2
              | (Match (env',branches,cfg1,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____82715  ->
                        let uu____82716 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____82716);
                   (let scrutinee_env = env  in
                    let env1 = env'  in
                    let scrutinee = t1  in
                    let norm_and_rebuild_match uu____82727 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____82732  ->
                           let uu____82733 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           let uu____82735 =
                             let uu____82737 =
                               FStar_All.pipe_right branches
                                 (FStar_List.map
                                    (fun uu____82767  ->
                                       match uu____82767 with
                                       | (p,uu____82778,uu____82779) ->
                                           FStar_Syntax_Print.pat_to_string p))
                                in
                             FStar_All.pipe_right uu____82737
                               (FStar_String.concat "\n\t")
                              in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu____82733 uu____82735);
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
                                (fun uu___602_82801  ->
                                   match uu___602_82801 with
                                   | FStar_TypeChecker_Env.InliningDelta  ->
                                       true
                                   | FStar_TypeChecker_Env.Eager_unfolding_only
                                        -> true
                                   | uu____82805 -> false))
                            in
                         let steps =
                           let uu___3487_82808 =
                             cfg1.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___3487_82808.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___3487_82808.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta = false;
                             FStar_TypeChecker_Cfg.weak =
                               (uu___3487_82808.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___3487_82808.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___3487_82808.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___3487_82808.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_only =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___3487_82808.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_tac = false;
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___3487_82808.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___3487_82808.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___3487_82808.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___3487_82808.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___3487_82808.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___3487_82808.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___3487_82808.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___3487_82808.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___3487_82808.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___3487_82808.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___3487_82808.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___3487_82808.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___3487_82808.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___3487_82808.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         let uu___3490_82815 = cfg1  in
                         {
                           FStar_TypeChecker_Cfg.steps = steps;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___3490_82815.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___3490_82815.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = new_delta;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___3490_82815.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong = true;
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___3490_82815.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets =
                             (uu___3490_82815.FStar_TypeChecker_Cfg.normalize_pure_lets);
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___3490_82815.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let norm_or_whnf env2 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env2 t2
                         else norm cfg_exclude_zeta env2 [] t2  in
                       let rec norm_pat env2 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu____82890 ->
                             (p, env2)
                         | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                             let uu____82921 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____83010  ->
                                       fun uu____83011  ->
                                         match (uu____83010, uu____83011)
                                         with
                                         | ((pats1,env3),(p1,b)) ->
                                             let uu____83161 =
                                               norm_pat env3 p1  in
                                             (match uu____83161 with
                                              | (p2,env4) ->
                                                  (((p2, b) :: pats1), env4)))
                                    ([], env2))
                                in
                             (match uu____82921 with
                              | (pats1,env3) ->
                                  ((let uu___3518_83331 = p  in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___3518_83331.FStar_Syntax_Syntax.p)
                                    }), env3))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___3522_83352 = x  in
                               let uu____83353 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3522_83352.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3522_83352.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____83353
                               }  in
                             ((let uu___3525_83367 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3525_83367.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___3529_83378 = x  in
                               let uu____83379 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3529_83378.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3529_83378.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____83379
                               }  in
                             ((let uu___3532_83393 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3532_83393.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                             let x1 =
                               let uu___3538_83409 = x  in
                               let uu____83410 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3538_83409.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3538_83409.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____83410
                               }  in
                             let t3 = norm_or_whnf env2 t2  in
                             ((let uu___3542_83425 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___3542_83425.FStar_Syntax_Syntax.p)
                               }), env2)
                          in
                       let branches1 =
                         match env1 with
                         | [] when whnf -> branches
                         | uu____83469 ->
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun branch1  ->
                                     let uu____83499 =
                                       FStar_Syntax_Subst.open_branch branch1
                                        in
                                     match uu____83499 with
                                     | (p,wopt,e) ->
                                         let uu____83519 = norm_pat env1 p
                                            in
                                         (match uu____83519 with
                                          | (p1,env2) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu____83574 =
                                                      norm_or_whnf env2 w  in
                                                    FStar_Pervasives_Native.Some
                                                      uu____83574
                                                 in
                                              let e1 = norm_or_whnf env2 e
                                                 in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1))))
                          in
                       let scrutinee1 =
                         let uu____83591 =
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
                         if uu____83591
                         then
                           norm
                             (let uu___3561_83598 = cfg1  in
                              {
                                FStar_TypeChecker_Cfg.steps =
                                  (let uu___3563_83601 =
                                     cfg1.FStar_TypeChecker_Cfg.steps  in
                                   {
                                     FStar_TypeChecker_Cfg.beta =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.beta);
                                     FStar_TypeChecker_Cfg.iota =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.iota);
                                     FStar_TypeChecker_Cfg.zeta =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.zeta);
                                     FStar_TypeChecker_Cfg.weak =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.weak);
                                     FStar_TypeChecker_Cfg.hnf =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.hnf);
                                     FStar_TypeChecker_Cfg.primops =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.primops);
                                     FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                       =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                     FStar_TypeChecker_Cfg.unfold_until =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.unfold_until);
                                     FStar_TypeChecker_Cfg.unfold_only =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.unfold_only);
                                     FStar_TypeChecker_Cfg.unfold_fully =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.unfold_fully);
                                     FStar_TypeChecker_Cfg.unfold_attr =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.unfold_attr);
                                     FStar_TypeChecker_Cfg.unfold_tac =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.unfold_tac);
                                     FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                       =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                     FStar_TypeChecker_Cfg.simplify =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.simplify);
                                     FStar_TypeChecker_Cfg.erase_universes =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.erase_universes);
                                     FStar_TypeChecker_Cfg.allow_unbound_universes
                                       =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                     FStar_TypeChecker_Cfg.reify_ =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.reify_);
                                     FStar_TypeChecker_Cfg.compress_uvars =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.compress_uvars);
                                     FStar_TypeChecker_Cfg.no_full_norm =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.no_full_norm);
                                     FStar_TypeChecker_Cfg.check_no_uvars =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.check_no_uvars);
                                     FStar_TypeChecker_Cfg.unmeta =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.unmeta);
                                     FStar_TypeChecker_Cfg.unascribe =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.unascribe);
                                     FStar_TypeChecker_Cfg.in_full_norm_request
                                       =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.in_full_norm_request);
                                     FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                       = false;
                                     FStar_TypeChecker_Cfg.nbe_step =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.nbe_step);
                                     FStar_TypeChecker_Cfg.for_extraction =
                                       (uu___3563_83601.FStar_TypeChecker_Cfg.for_extraction)
                                   });
                                FStar_TypeChecker_Cfg.tcenv =
                                  (uu___3561_83598.FStar_TypeChecker_Cfg.tcenv);
                                FStar_TypeChecker_Cfg.debug =
                                  (uu___3561_83598.FStar_TypeChecker_Cfg.debug);
                                FStar_TypeChecker_Cfg.delta_level =
                                  (uu___3561_83598.FStar_TypeChecker_Cfg.delta_level);
                                FStar_TypeChecker_Cfg.primitive_steps =
                                  (uu___3561_83598.FStar_TypeChecker_Cfg.primitive_steps);
                                FStar_TypeChecker_Cfg.strong =
                                  (uu___3561_83598.FStar_TypeChecker_Cfg.strong);
                                FStar_TypeChecker_Cfg.memoize_lazy =
                                  (uu___3561_83598.FStar_TypeChecker_Cfg.memoize_lazy);
                                FStar_TypeChecker_Cfg.normalize_pure_lets =
                                  (uu___3561_83598.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                FStar_TypeChecker_Cfg.reifying =
                                  (uu___3561_83598.FStar_TypeChecker_Cfg.reifying)
                              }) scrutinee_env [] scrutinee
                         else scrutinee  in
                       let uu____83605 =
                         mk
                           (FStar_Syntax_Syntax.Tm_match
                              (scrutinee1, branches1)) r
                          in
                       rebuild cfg1 env1 stack1 uu____83605)
                       in
                    let rec is_cons head1 =
                      let uu____83631 =
                        let uu____83632 = FStar_Syntax_Subst.compress head1
                           in
                        uu____83632.FStar_Syntax_Syntax.n  in
                      match uu____83631 with
                      | FStar_Syntax_Syntax.Tm_uinst (h,uu____83637) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____83642 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____83644;
                            FStar_Syntax_Syntax.fv_delta = uu____83645;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor );_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____83647;
                            FStar_Syntax_Syntax.fv_delta = uu____83648;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____83649);_}
                          -> true
                      | uu____83657 -> false  in
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
                      let uu____83826 =
                        FStar_Syntax_Util.head_and_args scrutinee2  in
                      match uu____83826 with
                      | (head1,args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu____83923 ->
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
                                | uu____83965 ->
                                    let uu____83966 =
                                      let uu____83968 = is_cons head1  in
                                      Prims.op_Negation uu____83968  in
                                    FStar_Util.Inr uu____83966)
                           | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                               let uu____83997 =
                                 let uu____83998 =
                                   FStar_Syntax_Util.un_uinst head1  in
                                 uu____83998.FStar_Syntax_Syntax.n  in
                               (match uu____83997 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____84017 ->
                                    let uu____84018 =
                                      let uu____84020 = is_cons head1  in
                                      Prims.op_Negation uu____84020  in
                                    FStar_Util.Inr uu____84018))
                    
                    and matches_args out a p =
                      match (a, p) with
                      | ([],[]) -> FStar_Util.Inl out
                      | ((t2,uu____84111)::rest_a,(p1,uu____84114)::rest_p)
                          ->
                          let uu____84173 = matches_pat t2 p1  in
                          (match uu____84173 with
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu____84226 -> FStar_Util.Inr false
                     in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1,wopt,b)::rest ->
                          let uu____84349 = matches_pat scrutinee1 p1  in
                          (match uu____84349 with
                           | FStar_Util.Inr (false ) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true ) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu____84395  ->
                                     let uu____84396 =
                                       FStar_Syntax_Print.pat_to_string p1
                                        in
                                     let uu____84398 =
                                       let uu____84400 =
                                         FStar_List.map
                                           (fun uu____84412  ->
                                              match uu____84412 with
                                              | (uu____84418,t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s
                                          in
                                       FStar_All.pipe_right uu____84400
                                         (FStar_String.concat "; ")
                                        in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu____84396 uu____84398);
                                (let env0 = env1  in
                                 let env2 =
                                   FStar_List.fold_left
                                     (fun env2  ->
                                        fun uu____84454  ->
                                          match uu____84454 with
                                          | (bv,t2) ->
                                              let uu____84477 =
                                                let uu____84484 =
                                                  let uu____84487 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____84487
                                                   in
                                                let uu____84488 =
                                                  let uu____84489 =
                                                    let uu____84521 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2))
                                                       in
                                                    ([], t2, uu____84521,
                                                      false)
                                                     in
                                                  Clos uu____84489  in
                                                (uu____84484, uu____84488)
                                                 in
                                              uu____84477 :: env2) env1 s
                                    in
                                 let uu____84614 =
                                   guard_when_clause wopt b rest  in
                                 norm cfg1 env2 stack1 uu____84614)))
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
            (fun uu____84647  ->
               let uu____84648 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____84648);
          (let uu____84651 = is_nbe_request s  in
           if uu____84651
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____84657  ->
                   let uu____84658 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____84658);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____84664  ->
                   let uu____84665 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____84665);
              (let uu____84668 =
                 FStar_Util.record_time (fun uu____84675  -> nbe_eval c s t)
                  in
               match uu____84668 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____84684  ->
                         let uu____84685 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____84687 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____84685 uu____84687);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____84695  ->
                   let uu____84696 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____84696);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____84702  ->
                   let uu____84703 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____84703);
              (let uu____84706 =
                 FStar_Util.record_time (fun uu____84713  -> norm c [] [] t)
                  in
               match uu____84706 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____84728  ->
                         let uu____84729 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____84731 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____84729 uu____84731);
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
        let uu____84766 = FStar_TypeChecker_Cfg.config s e  in
        norm_comp uu____84766 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____84784 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____84784 [] u
  
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
        let uu____84810 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____84810  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____84817 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___3719_84836 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3719_84836.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3719_84836.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name
              cfg.FStar_TypeChecker_Cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____84843 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____84843
          then
            let ct1 =
              let uu____84847 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____84847 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____84854 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____84854
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3729_84861 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3729_84861.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3729_84861.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3729_84861.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev
                      cfg.FStar_TypeChecker_Cfg.tcenv c
                     in
                  let uu___3733_84863 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3733_84863.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3733_84863.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3733_84863.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3733_84863.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3736_84864 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3736_84864.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3736_84864.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____84867 -> c
  
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
        let uu____84887 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____84887  in
      let uu____84894 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____84894
      then
        let uu____84897 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____84897 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____84903  ->
                 let uu____84904 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____84904)
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
          (fun uu___3752_84921  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___3751_84924 ->
            ((let uu____84926 =
                let uu____84932 =
                  let uu____84934 = FStar_Util.message_of_exn uu___3751_84924
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____84934
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____84932)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____84926);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          (fun uu___3762_84953  ->
             match () with
             | () ->
                 let uu____84954 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____84954 [] c) ()
        with
        | uu___3761_84963 ->
            ((let uu____84965 =
                let uu____84971 =
                  let uu____84973 = FStar_Util.message_of_exn uu___3761_84963
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____84973
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____84971)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____84965);
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
                   let uu____85022 =
                     let uu____85023 =
                       let uu____85030 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____85030)  in
                     FStar_Syntax_Syntax.Tm_refine uu____85023  in
                   mk uu____85022 t01.FStar_Syntax_Syntax.pos
               | uu____85035 -> t2)
          | uu____85036 -> t2  in
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
        let uu____85130 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____85130 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____85167 ->
                 let uu____85176 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____85176 with
                  | (actuals,uu____85186,uu____85187) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____85207 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____85207 with
                         | (binders,args) ->
                             let uu____85218 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____85218
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
      | uu____85233 ->
          let uu____85234 = FStar_Syntax_Util.head_and_args t  in
          (match uu____85234 with
           | (head1,args) ->
               let uu____85277 =
                 let uu____85278 = FStar_Syntax_Subst.compress head1  in
                 uu____85278.FStar_Syntax_Syntax.n  in
               (match uu____85277 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____85299 =
                      let uu____85314 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____85314  in
                    (match uu____85299 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____85354 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___3832_85362 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3832_85362.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3832_85362.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3832_85362.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3832_85362.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3832_85362.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3832_85362.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3832_85362.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3832_85362.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3832_85362.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___3832_85362.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3832_85362.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3832_85362.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3832_85362.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3832_85362.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3832_85362.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3832_85362.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3832_85362.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3832_85362.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3832_85362.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3832_85362.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3832_85362.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3832_85362.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3832_85362.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3832_85362.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3832_85362.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3832_85362.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3832_85362.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3832_85362.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3832_85362.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3832_85362.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3832_85362.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3832_85362.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3832_85362.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3832_85362.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3832_85362.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___3832_85362.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3832_85362.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3832_85362.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3832_85362.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3832_85362.FStar_TypeChecker_Env.nbe)
                                 }) t
                               in
                            match uu____85354 with
                            | (uu____85365,ty,uu____85367) ->
                                eta_expand_with_type env t ty))
                | uu____85368 ->
                    let uu____85369 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___3839_85377 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3839_85377.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3839_85377.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3839_85377.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3839_85377.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3839_85377.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3839_85377.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3839_85377.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3839_85377.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3839_85377.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___3839_85377.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3839_85377.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3839_85377.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3839_85377.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3839_85377.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3839_85377.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3839_85377.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3839_85377.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3839_85377.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3839_85377.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3839_85377.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3839_85377.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3839_85377.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3839_85377.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3839_85377.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3839_85377.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3839_85377.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3839_85377.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3839_85377.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3839_85377.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3839_85377.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3839_85377.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3839_85377.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3839_85377.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3839_85377.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3839_85377.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___3839_85377.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3839_85377.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3839_85377.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3839_85377.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3839_85377.FStar_TypeChecker_Env.nbe)
                         }) t
                       in
                    (match uu____85369 with
                     | (uu____85380,ty,uu____85382) ->
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
      let uu___3851_85464 = x  in
      let uu____85465 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3851_85464.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3851_85464.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____85465
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____85468 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____85492 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____85493 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____85494 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____85495 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____85502 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____85503 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____85504 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3877_85538 = rc  in
          let uu____85539 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____85548 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3877_85538.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____85539;
            FStar_Syntax_Syntax.residual_flags = uu____85548
          }  in
        let uu____85551 =
          let uu____85552 =
            let uu____85571 = elim_delayed_subst_binders bs  in
            let uu____85580 = elim_delayed_subst_term t2  in
            let uu____85583 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____85571, uu____85580, uu____85583)  in
          FStar_Syntax_Syntax.Tm_abs uu____85552  in
        mk1 uu____85551
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____85620 =
          let uu____85621 =
            let uu____85636 = elim_delayed_subst_binders bs  in
            let uu____85645 = elim_delayed_subst_comp c  in
            (uu____85636, uu____85645)  in
          FStar_Syntax_Syntax.Tm_arrow uu____85621  in
        mk1 uu____85620
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____85664 =
          let uu____85665 =
            let uu____85672 = elim_bv bv  in
            let uu____85673 = elim_delayed_subst_term phi  in
            (uu____85672, uu____85673)  in
          FStar_Syntax_Syntax.Tm_refine uu____85665  in
        mk1 uu____85664
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____85704 =
          let uu____85705 =
            let uu____85722 = elim_delayed_subst_term t2  in
            let uu____85725 = elim_delayed_subst_args args  in
            (uu____85722, uu____85725)  in
          FStar_Syntax_Syntax.Tm_app uu____85705  in
        mk1 uu____85704
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3899_85797 = p  in
              let uu____85798 =
                let uu____85799 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____85799  in
              {
                FStar_Syntax_Syntax.v = uu____85798;
                FStar_Syntax_Syntax.p =
                  (uu___3899_85797.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3903_85801 = p  in
              let uu____85802 =
                let uu____85803 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____85803  in
              {
                FStar_Syntax_Syntax.v = uu____85802;
                FStar_Syntax_Syntax.p =
                  (uu___3903_85801.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3909_85810 = p  in
              let uu____85811 =
                let uu____85812 =
                  let uu____85819 = elim_bv x  in
                  let uu____85820 = elim_delayed_subst_term t0  in
                  (uu____85819, uu____85820)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____85812  in
              {
                FStar_Syntax_Syntax.v = uu____85811;
                FStar_Syntax_Syntax.p =
                  (uu___3909_85810.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3915_85845 = p  in
              let uu____85846 =
                let uu____85847 =
                  let uu____85861 =
                    FStar_List.map
                      (fun uu____85887  ->
                         match uu____85887 with
                         | (x,b) ->
                             let uu____85904 = elim_pat x  in
                             (uu____85904, b)) pats
                     in
                  (fv, uu____85861)  in
                FStar_Syntax_Syntax.Pat_cons uu____85847  in
              {
                FStar_Syntax_Syntax.v = uu____85846;
                FStar_Syntax_Syntax.p =
                  (uu___3915_85845.FStar_Syntax_Syntax.p)
              }
          | uu____85919 -> p  in
        let elim_branch uu____85943 =
          match uu____85943 with
          | (pat,wopt,t3) ->
              let uu____85969 = elim_pat pat  in
              let uu____85972 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____85975 = elim_delayed_subst_term t3  in
              (uu____85969, uu____85972, uu____85975)
           in
        let uu____85980 =
          let uu____85981 =
            let uu____86004 = elim_delayed_subst_term t2  in
            let uu____86007 = FStar_List.map elim_branch branches  in
            (uu____86004, uu____86007)  in
          FStar_Syntax_Syntax.Tm_match uu____85981  in
        mk1 uu____85980
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____86138 =
          match uu____86138 with
          | (tc,topt) ->
              let uu____86173 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____86183 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____86183
                | FStar_Util.Inr c ->
                    let uu____86185 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____86185
                 in
              let uu____86186 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____86173, uu____86186)
           in
        let uu____86195 =
          let uu____86196 =
            let uu____86223 = elim_delayed_subst_term t2  in
            let uu____86226 = elim_ascription a  in
            (uu____86223, uu____86226, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____86196  in
        mk1 uu____86195
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3945_86289 = lb  in
          let uu____86290 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____86293 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3945_86289.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3945_86289.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____86290;
            FStar_Syntax_Syntax.lbeff =
              (uu___3945_86289.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____86293;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3945_86289.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3945_86289.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____86296 =
          let uu____86297 =
            let uu____86311 =
              let uu____86319 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____86319)  in
            let uu____86331 = elim_delayed_subst_term t2  in
            (uu____86311, uu____86331)  in
          FStar_Syntax_Syntax.Tm_let uu____86297  in
        mk1 uu____86296
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____86376 =
          let uu____86377 =
            let uu____86384 = elim_delayed_subst_term tm  in
            (uu____86384, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____86377  in
        mk1 uu____86376
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____86395 =
          let uu____86396 =
            let uu____86403 = elim_delayed_subst_term t2  in
            let uu____86406 = elim_delayed_subst_meta md  in
            (uu____86403, uu____86406)  in
          FStar_Syntax_Syntax.Tm_meta uu____86396  in
        mk1 uu____86395

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
      (fun uu___603_86415  ->
         match uu___603_86415 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____86419 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____86419
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
        let uu____86442 =
          let uu____86443 =
            let uu____86452 = elim_delayed_subst_term t  in
            (uu____86452, uopt)  in
          FStar_Syntax_Syntax.Total uu____86443  in
        mk1 uu____86442
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____86469 =
          let uu____86470 =
            let uu____86479 = elim_delayed_subst_term t  in
            (uu____86479, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____86470  in
        mk1 uu____86469
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3978_86488 = ct  in
          let uu____86489 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____86492 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____86503 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3978_86488.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3978_86488.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____86489;
            FStar_Syntax_Syntax.effect_args = uu____86492;
            FStar_Syntax_Syntax.flags = uu____86503
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___604_86506  ->
    match uu___604_86506 with
    | FStar_Syntax_Syntax.Meta_pattern args ->
        let uu____86520 = FStar_List.map elim_delayed_subst_args args  in
        FStar_Syntax_Syntax.Meta_pattern uu____86520
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____86559 =
          let uu____86566 = elim_delayed_subst_term t  in (m, uu____86566)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____86559
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____86578 =
          let uu____86587 = elim_delayed_subst_term t  in
          (m1, m2, uu____86587)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____86578
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
      (fun uu____86620  ->
         match uu____86620 with
         | (t,q) ->
             let uu____86639 = elim_delayed_subst_term t  in (uu____86639, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____86667  ->
         match uu____86667 with
         | (x,q) ->
             let uu____86686 =
               let uu___4002_86687 = x  in
               let uu____86688 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___4002_86687.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___4002_86687.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____86688
               }  in
             (uu____86686, q)) bs

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
            | (uu____86796,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____86828,FStar_Util.Inl t) ->
                let uu____86850 =
                  let uu____86857 =
                    let uu____86858 =
                      let uu____86873 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____86873)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____86858  in
                  FStar_Syntax_Syntax.mk uu____86857  in
                uu____86850 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____86886 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____86886 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____86918 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____86991 ->
                    let uu____86992 =
                      let uu____87001 =
                        let uu____87002 = FStar_Syntax_Subst.compress t4  in
                        uu____87002.FStar_Syntax_Syntax.n  in
                      (uu____87001, tc)  in
                    (match uu____86992 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____87031) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____87078) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____87123,FStar_Util.Inl uu____87124) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____87155 -> failwith "Impossible")
                 in
              (match uu____86918 with
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
          let uu____87294 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____87294 with
          | (univ_names1,binders1,tc) ->
              let uu____87368 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____87368)
  
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
          let uu____87422 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____87422 with
          | (univ_names1,binders1,tc) ->
              let uu____87496 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____87496)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____87538 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____87538 with
           | (univ_names1,binders1,typ1) ->
               let uu___4085_87578 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4085_87578.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4085_87578.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4085_87578.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4085_87578.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___4091_87593 = s  in
          let uu____87594 =
            let uu____87595 =
              let uu____87604 = FStar_List.map (elim_uvars env) sigs  in
              (uu____87604, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____87595  in
          {
            FStar_Syntax_Syntax.sigel = uu____87594;
            FStar_Syntax_Syntax.sigrng =
              (uu___4091_87593.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___4091_87593.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___4091_87593.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___4091_87593.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____87623 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____87623 with
           | (univ_names1,uu____87647,typ1) ->
               let uu___4105_87669 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4105_87669.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4105_87669.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4105_87669.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4105_87669.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____87676 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____87676 with
           | (univ_names1,uu____87700,typ1) ->
               let uu___4116_87722 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4116_87722.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4116_87722.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4116_87722.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4116_87722.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____87752 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____87752 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____87777 =
                            let uu____87778 =
                              let uu____87779 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____87779  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____87778
                             in
                          elim_delayed_subst_term uu____87777  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___4132_87782 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___4132_87782.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___4132_87782.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___4132_87782.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___4132_87782.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___4135_87783 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___4135_87783.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___4135_87783.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___4135_87783.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___4135_87783.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___4139_87790 = s  in
          let uu____87791 =
            let uu____87792 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____87792  in
          {
            FStar_Syntax_Syntax.sigel = uu____87791;
            FStar_Syntax_Syntax.sigrng =
              (uu___4139_87790.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___4139_87790.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___4139_87790.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___4139_87790.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____87796 = elim_uvars_aux_t env us [] t  in
          (match uu____87796 with
           | (us1,uu____87820,t1) ->
               let uu___4150_87842 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4150_87842.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4150_87842.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4150_87842.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4150_87842.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____87843 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____87846 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____87846 with
           | (univs1,binders,signature) ->
               let uu____87886 =
                 let uu____87891 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____87891 with
                 | (univs_opening,univs2) ->
                     let uu____87914 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____87914)
                  in
               (match uu____87886 with
                | (univs_opening,univs_closing) ->
                    let uu____87917 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____87923 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____87924 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____87923, uu____87924)  in
                    (match uu____87917 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____87950 =
                           match uu____87950 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____87968 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____87968 with
                                | (us1,t1) ->
                                    let uu____87979 =
                                      let uu____87988 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____87993 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____87988, uu____87993)  in
                                    (match uu____87979 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____88016 =
                                           let uu____88025 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____88030 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____88025, uu____88030)  in
                                         (match uu____88016 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____88054 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____88054
                                                 in
                                              let uu____88055 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____88055 with
                                               | (uu____88082,uu____88083,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____88106 =
                                                       let uu____88107 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____88107
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____88106
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____88116 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____88116 with
                           | (uu____88135,uu____88136,t1) -> t1  in
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
                             | uu____88212 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____88239 =
                               let uu____88240 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____88240.FStar_Syntax_Syntax.n  in
                             match uu____88239 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____88299 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____88333 =
                               let uu____88334 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____88334.FStar_Syntax_Syntax.n  in
                             match uu____88333 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____88357) ->
                                 let uu____88382 = destruct_action_body body
                                    in
                                 (match uu____88382 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____88431 ->
                                 let uu____88432 = destruct_action_body t  in
                                 (match uu____88432 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____88487 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____88487 with
                           | (action_univs,t) ->
                               let uu____88496 = destruct_action_typ_templ t
                                  in
                               (match uu____88496 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___4236_88543 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___4236_88543.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___4236_88543.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___4239_88545 = ed  in
                           let uu____88546 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____88547 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____88548 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____88549 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____88550 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____88551 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____88552 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____88553 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____88554 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____88555 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____88556 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____88557 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____88558 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____88559 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___4239_88545.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___4239_88545.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____88546;
                             FStar_Syntax_Syntax.bind_wp = uu____88547;
                             FStar_Syntax_Syntax.if_then_else = uu____88548;
                             FStar_Syntax_Syntax.ite_wp = uu____88549;
                             FStar_Syntax_Syntax.stronger = uu____88550;
                             FStar_Syntax_Syntax.close_wp = uu____88551;
                             FStar_Syntax_Syntax.assert_p = uu____88552;
                             FStar_Syntax_Syntax.assume_p = uu____88553;
                             FStar_Syntax_Syntax.null_wp = uu____88554;
                             FStar_Syntax_Syntax.trivial = uu____88555;
                             FStar_Syntax_Syntax.repr = uu____88556;
                             FStar_Syntax_Syntax.return_repr = uu____88557;
                             FStar_Syntax_Syntax.bind_repr = uu____88558;
                             FStar_Syntax_Syntax.actions = uu____88559;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___4239_88545.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___4242_88562 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___4242_88562.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___4242_88562.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___4242_88562.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___4242_88562.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___605_88583 =
            match uu___605_88583 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____88614 = elim_uvars_aux_t env us [] t  in
                (match uu____88614 with
                 | (us1,uu____88646,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___4257_88677 = sub_eff  in
            let uu____88678 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____88681 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___4257_88677.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___4257_88677.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____88678;
              FStar_Syntax_Syntax.lift = uu____88681
            }  in
          let uu___4260_88684 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___4260_88684.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___4260_88684.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___4260_88684.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___4260_88684.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____88694 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____88694 with
           | (univ_names1,binders1,comp1) ->
               let uu___4273_88734 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___4273_88734.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___4273_88734.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___4273_88734.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___4273_88734.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____88737 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____88738 -> s
  
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
        let uu____88787 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____88787 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____88809 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____88809 with
             | (uu____88816,head_def) ->
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
      let uu____88822 = FStar_Syntax_Util.head_and_args t  in
      match uu____88822 with
      | (head1,args) ->
          let uu____88867 =
            let uu____88868 = FStar_Syntax_Subst.compress head1  in
            uu____88868.FStar_Syntax_Syntax.n  in
          (match uu____88867 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____88875;
                  FStar_Syntax_Syntax.vars = uu____88876;_},us)
               -> aux fv us args
           | uu____88882 -> FStar_Pervasives_Native.None)
  