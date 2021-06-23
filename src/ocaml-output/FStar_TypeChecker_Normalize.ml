open Prims
let (maybe_debug :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Util.time)
        FStar_Pervasives_Native.option -> unit)
  =
  fun cfg ->
    fun t ->
      fun dbg ->
        if
          (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
        then
          match dbg with
          | FStar_Pervasives_Native.Some (tm, time_then) ->
              let time_now = FStar_Util.now () in
              let uu___ =
                let uu___1 =
                  let uu___2 = FStar_Util.time_diff time_then time_now in
                  FStar_Pervasives_Native.snd uu___2 in
                FStar_Util.string_of_int uu___1 in
              let uu___1 = FStar_Syntax_Print.term_to_string tm in
              let uu___2 = FStar_TypeChecker_Cfg.cfg_to_string cfg in
              let uu___3 = FStar_Syntax_Print.term_to_string t in
              FStar_Util.print4
                "Normalizer result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                uu___ uu___1 uu___2 uu___3
          | uu___ -> ()
        else ()
let cases :
  'uuuuu 'uuuuu1 .
    ('uuuuu -> 'uuuuu1) ->
      'uuuuu1 -> 'uuuuu FStar_Pervasives_Native.option -> 'uuuuu1
  =
  fun f ->
    fun d ->
      fun uu___ ->
        match uu___ with
        | FStar_Pervasives_Native.Some x -> f x
        | FStar_Pervasives_Native.None -> d
type closure =
  | Clos of ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option *
  closure) Prims.list * FStar_Syntax_Syntax.term *
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
  Prims.list * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo *
  Prims.bool) 
  | Univ of FStar_Syntax_Syntax.universe 
  | Dummy 
let (uu___is_Clos : closure -> Prims.bool) =
  fun projectee -> match projectee with | Clos _0 -> true | uu___ -> false
let (__proj__Clos__item___0 :
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
      Prims.list * FStar_Syntax_Syntax.term * ((FStar_Syntax_Syntax.binder
      FStar_Pervasives_Native.option * closure) Prims.list *
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool))
  = fun projectee -> match projectee with | Clos _0 -> _0
let (uu___is_Univ : closure -> Prims.bool) =
  fun projectee -> match projectee with | Univ _0 -> true | uu___ -> false
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee -> match projectee with | Univ _0 -> _0
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee -> match projectee with | Dummy -> true | uu___ -> false
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
  | Match of (env * FStar_Syntax_Syntax.ascription
  FStar_Pervasives_Native.option * branches * FStar_TypeChecker_Cfg.cfg *
  FStar_Range.range) 
  | Abs of (env * FStar_Syntax_Syntax.binders * env *
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
  FStar_Range.range) 
  | App of (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
  FStar_Range.range) 
  | CBVApp of (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
  FStar_Range.range) 
  | Meta of (env * FStar_Syntax_Syntax.metadata * FStar_Range.range) 
  | Let of (env * FStar_Syntax_Syntax.binders *
  FStar_Syntax_Syntax.letbinding * FStar_Range.range) 
  | Cfg of (FStar_TypeChecker_Cfg.cfg * (FStar_Syntax_Syntax.term *
  FStar_Util.time) FStar_Pervasives_Native.option) 
let (uu___is_Arg : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | Arg _0 -> true | uu___ -> false
let (__proj__Arg__item___0 :
  stack_elt -> (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)) =
  fun projectee -> match projectee with | Arg _0 -> _0
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | UnivArgs _0 -> true | uu___ -> false
let (__proj__UnivArgs__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range))
  = fun projectee -> match projectee with | UnivArgs _0 -> _0
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | MemoLazy _0 -> true | uu___ -> false
let (__proj__MemoLazy__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo) =
  fun projectee -> match projectee with | MemoLazy _0 -> _0
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | Match _0 -> true | uu___ -> false
let (__proj__Match__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.ascription FStar_Pervasives_Native.option *
      branches * FStar_TypeChecker_Cfg.cfg * FStar_Range.range))
  = fun projectee -> match projectee with | Match _0 -> _0
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | Abs _0 -> true | uu___ -> false
let (__proj__Abs__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * env *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
      FStar_Range.range))
  = fun projectee -> match projectee with | Abs _0 -> _0
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | App _0 -> true | uu___ -> false
let (__proj__App__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Range.range))
  = fun projectee -> match projectee with | App _0 -> _0
let (uu___is_CBVApp : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | CBVApp _0 -> true | uu___ -> false
let (__proj__CBVApp__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Range.range))
  = fun projectee -> match projectee with | CBVApp _0 -> _0
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | Meta _0 -> true | uu___ -> false
let (__proj__Meta__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.metadata * FStar_Range.range)) =
  fun projectee -> match projectee with | Meta _0 -> _0
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | Let _0 -> true | uu___ -> false
let (__proj__Let__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding *
      FStar_Range.range))
  = fun projectee -> match projectee with | Let _0 -> _0
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | Cfg _0 -> true | uu___ -> false
let (__proj__Cfg__item___0 :
  stack_elt ->
    (FStar_TypeChecker_Cfg.cfg * (FStar_Syntax_Syntax.term * FStar_Util.time)
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Cfg _0 -> _0
type stack = stack_elt Prims.list
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu___ = FStar_Syntax_Util.head_and_args_full t in
    match uu___ with | (hd, uu___1) -> hd
let set_memo :
  'a . FStar_TypeChecker_Cfg.cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> unit
  =
  fun cfg ->
    fun r ->
      fun t ->
        if cfg.FStar_TypeChecker_Cfg.memoize_lazy
        then
          let uu___ = FStar_ST.op_Bang r in
          match uu___ with
          | FStar_Pervasives_Native.Some uu___1 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
let (closure_to_string : closure -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | Clos (env1, t, uu___1, uu___2) ->
        let uu___3 =
          FStar_All.pipe_right (FStar_List.length env1)
            FStar_Util.string_of_int in
        let uu___4 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format2 "(env=%s elts; %s)" uu___3 uu___4
    | Univ uu___1 -> "Univ"
    | Dummy -> "dummy"
let (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> Prims.string)
  =
  fun env1 ->
    let uu___ =
      FStar_List.map
        (fun uu___1 ->
           match uu___1 with
           | (bopt, c) ->
               let uu___2 =
                 match bopt with
                 | FStar_Pervasives_Native.None -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x in
               let uu___3 = closure_to_string c in
               FStar_Util.format2 "(%s, %s)" uu___2 uu___3) env1 in
    FStar_All.pipe_right uu___ (FStar_String.concat "; ")
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | Arg (c, uu___1, uu___2) ->
        let uu___3 = closure_to_string c in
        FStar_Util.format1 "Closure %s" uu___3
    | MemoLazy uu___1 -> "MemoLazy"
    | Abs (uu___1, bs, uu___2, uu___3, uu___4) ->
        let uu___5 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs) in
        FStar_Util.format1 "Abs %s" uu___5
    | UnivArgs uu___1 -> "UnivArgs"
    | Match uu___1 -> "Match"
    | App (uu___1, t, uu___2, uu___3) ->
        let uu___4 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "App %s" uu___4
    | CBVApp (uu___1, t, uu___2, uu___3) ->
        let uu___4 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "CBVApp %s" uu___4
    | Meta (uu___1, m, uu___2) -> "Meta"
    | Let uu___1 -> "Let"
    | Cfg uu___1 -> "Cfg"
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s ->
    let uu___ = FStar_List.map stack_elt_to_string s in
    FStar_All.pipe_right uu___ (FStar_String.concat "; ")
let is_empty : 'uuuuu . 'uuuuu Prims.list -> Prims.bool =
  fun uu___ -> match uu___ with | [] -> true | uu___1 -> false
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> FStar_Syntax_Syntax.bv -> closure)
  =
  fun env1 ->
    fun x ->
      try
        (fun uu___ ->
           match () with
           | () ->
               let uu___1 = FStar_List.nth env1 x.FStar_Syntax_Syntax.index in
               FStar_Pervasives_Native.snd uu___1) ()
      with
      | uu___ ->
          let uu___1 =
            let uu___2 = FStar_Syntax_Print.db_to_string x in
            let uu___3 = env_to_string env1 in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu___2 uu___3 in
          failwith uu___1
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l ->
    let uu___ = FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid in
    if uu___
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu___2 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid in
       if uu___2
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu___4 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid in
          if uu___4
          then
            FStar_Pervasives_Native.Some FStar_Parser_Const.effect_PURE_lid
          else FStar_Pervasives_Native.None))
let (norm_universe :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun cfg ->
    fun env1 ->
      fun u ->
        let norm_univs_for_max us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us in
          let uu___ =
            FStar_List.fold_left
              (fun uu___1 ->
                 fun u1 ->
                   match uu___1 with
                   | (cur_kernel, cur_max, out) ->
                       let uu___2 = FStar_Syntax_Util.univ_kernel u1 in
                       (match uu___2 with
                        | (k_u, n) ->
                            let uu___3 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu___3
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1 in
          match uu___ with | (uu___1, u1, out) -> FStar_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 (fun uu___ ->
                    match () with
                    | () ->
                        let uu___1 =
                          let uu___2 = FStar_List.nth env1 x in
                          FStar_Pervasives_Native.snd uu___2 in
                        (match uu___1 with
                         | Univ u3 ->
                             ((let uu___3 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      cfg.FStar_TypeChecker_Cfg.tcenv)
                                   (FStar_Options.Other "univ_norm") in
                               if uu___3
                               then
                                 let uu___4 =
                                   FStar_Syntax_Print.univ_to_string u3 in
                                 FStar_Util.print1
                                   "Univ (in norm_universe): %s\n" uu___4
                               else ());
                              aux u3)
                         | Dummy -> [u2]
                         | uu___2 ->
                             let uu___3 =
                               let uu___4 = FStar_Util.string_of_int x in
                               FStar_Util.format1
                                 "Impossible: universe variable u@%s bound to a term"
                                 uu___4 in
                             failwith uu___3)) ()
               with
               | uu___1 ->
                   if
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else
                     (let uu___3 =
                        let uu___4 = FStar_Util.string_of_int x in
                        FStar_String.op_Hat "Universe variable not found: u@"
                          uu___4 in
                      failwith uu___3))
          | FStar_Syntax_Syntax.U_unif uu___ when
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero -> [u2]
          | FStar_Syntax_Syntax.U_unif uu___ -> [u2]
          | FStar_Syntax_Syntax.U_name uu___ -> [u2]
          | FStar_Syntax_Syntax.U_unknown -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu___ = FStar_List.collect aux us in
                FStar_All.pipe_right uu___ norm_univs_for_max in
              (match us1 with
               | u_k::hd::rest ->
                   let rest1 = hd :: rest in
                   let uu___ = FStar_Syntax_Util.univ_kernel u_k in
                   (match uu___ with
                    | (FStar_Syntax_Syntax.U_zero, n) ->
                        let uu___1 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3 ->
                                  let uu___2 =
                                    FStar_Syntax_Util.univ_kernel u3 in
                                  match uu___2 with | (uu___3, m) -> n <= m)) in
                        if uu___1 then rest1 else us1
                    | uu___1 -> us1)
               | uu___ -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu___ = aux u3 in
              FStar_List.map
                (fun uu___1 -> FStar_Syntax_Syntax.U_succ uu___1) uu___ in
        if
          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu___1 = aux u in
           match uu___1 with
           | [] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero)::[] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero)::u1::[] -> u1
           | (FStar_Syntax_Syntax.U_zero)::us -> FStar_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStar_Syntax_Syntax.U_max us)
let rec (inline_closure_env :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun t ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu___1 ->
               let uu___2 = FStar_Syntax_Print.tag_of_term t in
               let uu___3 = env_to_string env1 in
               let uu___4 = FStar_Syntax_Print.term_to_string t in
               FStar_Util.print3 ">>> %s (env=%s)\nClosure_as_term %s\n"
                 uu___2 uu___3 uu___4);
          (match env1 with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               -> rebuild_closure cfg env1 stack1 t
           | uu___1 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu___2 ->
                    let uu___3 = FStar_Syntax_Subst.compress t in
                    inline_closure_env cfg env1 stack1 uu___3
                | FStar_Syntax_Syntax.Tm_unknown ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_constant uu___2 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_name uu___2 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_lazy uu___2 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_fvar uu___2 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_uvar (uv, s) ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu___2 ->
                           let uu___3 =
                             let uu___4 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos in
                             let uu___5 =
                               FStar_Syntax_Print.term_to_string t1 in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu___4 uu___5 in
                           failwith uu___3
                       | uu___2 -> inline_closure_env cfg env1 stack1 t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1 ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___3 ->
                                         match uu___3 with
                                         | FStar_Syntax_Syntax.NT (x, t1) ->
                                             let uu___4 =
                                               let uu___5 =
                                                 inline_closure_env cfg env1
                                                   [] t1 in
                                               (x, uu___5) in
                                             FStar_Syntax_Syntax.NT uu___4
                                         | FStar_Syntax_Syntax.NM (x, i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___4 = x in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___4.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___4.FStar_Syntax_Syntax.sort)
                                                  }) in
                                             let t1 =
                                               inline_closure_env cfg env1 []
                                                 x_i in
                                             (match t1.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_bvar
                                                  x_j ->
                                                  FStar_Syntax_Syntax.NM
                                                    (x,
                                                      (x_j.FStar_Syntax_Syntax.index))
                                              | uu___4 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu___4 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes")))) in
                       let t1 =
                         let uu___3 = t in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___3.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___3.FStar_Syntax_Syntax.vars)
                         } in
                       rebuild_closure cfg env1 stack1 t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu___2 =
                        let uu___3 = norm_universe cfg env1 u in
                        FStar_Syntax_Syntax.Tm_type uu___3 in
                      FStar_Syntax_Syntax.mk uu___2 t.FStar_Syntax_Syntax.pos in
                    rebuild_closure cfg env1 stack1 t1
                | FStar_Syntax_Syntax.Tm_uinst (t', us) ->
                    let t1 =
                      let uu___2 = FStar_List.map (norm_universe cfg env1) us in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu___2 in
                    rebuild_closure cfg env1 stack1 t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu___2 = lookup_bvar env1 x in
                    (match uu___2 with
                     | Univ uu___3 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy ->
                         let x1 =
                           let uu___3 = x in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           } in
                         let t1 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos in
                         rebuild_closure cfg env1 stack1 t1
                     | Clos (env2, t0, uu___3, uu___4) ->
                         inline_closure_env cfg env2 stack1 t0)
                | FStar_Syntax_Syntax.Tm_app (head, args) ->
                    let stack2 =
                      FStar_All.pipe_right stack1
                        (FStar_List.fold_right
                           (fun uu___2 ->
                              fun stack3 ->
                                match uu___2 with
                                | (a, aq) ->
                                    let uu___3 =
                                      let uu___4 =
                                        let uu___5 =
                                          let uu___6 =
                                            let uu___7 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None in
                                            (env1, a, uu___7, false) in
                                          Clos uu___6 in
                                        (uu___5, aq,
                                          (t.FStar_Syntax_Syntax.pos)) in
                                      Arg uu___4 in
                                    uu___3 :: stack3) args) in
                    inline_closure_env cfg env1 stack2 head
                | FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) ->
                    let env' =
                      FStar_All.pipe_right env1
                        (FStar_List.fold_right
                           (fun _b ->
                              fun env2 ->
                                (FStar_Pervasives_Native.None, Dummy) :: env2)
                           bs) in
                    let stack2 =
                      (Abs
                         (env1, bs, env', lopt, (t.FStar_Syntax_Syntax.pos)))
                      :: stack1 in
                    inline_closure_env cfg env' stack2 body
                | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                    let uu___2 = close_binders cfg env1 bs in
                    (match uu___2 with
                     | (bs1, env') ->
                         let c1 = close_comp cfg env' c in
                         let t1 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos in
                         rebuild_closure cfg env1 stack1 t1)
                | FStar_Syntax_Syntax.Tm_refine (x, uu___2) when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    ->
                    inline_closure_env cfg env1 stack1
                      x.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
                    let uu___2 =
                      let uu___3 =
                        let uu___4 = FStar_Syntax_Syntax.mk_binder x in
                        [uu___4] in
                      close_binders cfg env1 uu___3 in
                    (match uu___2 with
                     | (x1, env2) ->
                         let phi1 = non_tail_inline_closure_env cfg env2 phi in
                         let t1 =
                           let uu___3 =
                             let uu___4 =
                               let uu___5 =
                                 let uu___6 = FStar_List.hd x1 in
                                 uu___6.FStar_Syntax_Syntax.binder_bv in
                               (uu___5, phi1) in
                             FStar_Syntax_Syntax.Tm_refine uu___4 in
                           FStar_Syntax_Syntax.mk uu___3
                             t.FStar_Syntax_Syntax.pos in
                         rebuild_closure cfg env2 stack1 t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1, asc, lopt) ->
                    let asc1 = close_ascription cfg env1 asc in
                    let t2 =
                      let uu___2 =
                        let uu___3 =
                          let uu___4 =
                            non_tail_inline_closure_env cfg env1 t1 in
                          (uu___4, asc1, lopt) in
                        FStar_Syntax_Syntax.Tm_ascribed uu___3 in
                      FStar_Syntax_Syntax.mk uu___2 t.FStar_Syntax_Syntax.pos in
                    rebuild_closure cfg env1 stack1 t2
                | FStar_Syntax_Syntax.Tm_quoted (t', qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic ->
                          let uu___2 =
                            let uu___3 =
                              let uu___4 =
                                non_tail_inline_closure_env cfg env1 t' in
                              (uu___4, qi) in
                            FStar_Syntax_Syntax.Tm_quoted uu___3 in
                          FStar_Syntax_Syntax.mk uu___2
                            t.FStar_Syntax_Syntax.pos
                      | FStar_Syntax_Syntax.Quote_static ->
                          let qi1 =
                            FStar_Syntax_Syntax.on_antiquoted
                              (non_tail_inline_closure_env cfg env1) qi in
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_quoted (t', qi1))
                            t.FStar_Syntax_Syntax.pos in
                    rebuild_closure cfg env1 stack1 t1
                | FStar_Syntax_Syntax.Tm_meta (t', m) ->
                    let stack2 =
                      (Meta (env1, m, (t.FStar_Syntax_Syntax.pos))) :: stack1 in
                    inline_closure_env cfg env1 stack2 t'
                | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
                    let env0 = env1 in
                    let env2 =
                      FStar_List.fold_left
                        (fun env3 -> fun uu___2 -> dummy :: env3) env1
                        lb.FStar_Syntax_Syntax.lbunivs in
                    let typ =
                      non_tail_inline_closure_env cfg env2
                        lb.FStar_Syntax_Syntax.lbtyp in
                    let def =
                      non_tail_inline_closure_env cfg env2
                        lb.FStar_Syntax_Syntax.lbdef in
                    let uu___2 =
                      let uu___3 = FStar_Syntax_Syntax.is_top_level [lb] in
                      if uu___3
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                         let uu___5 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body in
                         ((FStar_Pervasives.Inl
                             (let uu___6 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___6.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___6.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu___5)) in
                    (match uu___2 with
                     | (nm, body1) ->
                         let attrs =
                           FStar_List.map
                             (non_tail_inline_closure_env cfg env0)
                             lb.FStar_Syntax_Syntax.lbattrs in
                         let lb1 =
                           let uu___3 = lb in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___3.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___3.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs = attrs;
                             FStar_Syntax_Syntax.lbpos =
                               (uu___3.FStar_Syntax_Syntax.lbpos)
                           } in
                         let t1 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos in
                         rebuild_closure cfg env0 stack1 t1)
                | FStar_Syntax_Syntax.Tm_let ((uu___2, lbs), body) ->
                    let norm_one_lb env2 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu___3 -> fun env3 -> dummy :: env3)
                          lb.FStar_Syntax_Syntax.lbunivs env2 in
                      let env3 =
                        let uu___3 = FStar_Syntax_Syntax.is_top_level lbs in
                        if uu___3
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu___5 -> fun env4 -> dummy :: env4) lbs
                            env_univs in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp in
                      let nm =
                        let uu___3 = FStar_Syntax_Syntax.is_top_level lbs in
                        if uu___3
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                           FStar_Pervasives.Inl
                             (let uu___5 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___5.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___5.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              })) in
                      let uu___3 = lb in
                      let uu___4 =
                        non_tail_inline_closure_env cfg env3
                          lb.FStar_Syntax_Syntax.lbdef in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___3.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___3.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu___4;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___3.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___3.FStar_Syntax_Syntax.lbpos)
                      } in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env1)) in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu___3 -> fun env2 -> dummy :: env2) lbs1 env1 in
                      non_tail_inline_closure_env cfg body_env body in
                    let t1 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                        t.FStar_Syntax_Syntax.pos in
                    rebuild_closure cfg env1 stack1 t1
                | FStar_Syntax_Syntax.Tm_match (head, asc_opt, branches1) ->
                    let stack2 =
                      (Match
                         (env1, asc_opt, branches1, cfg,
                           (t.FStar_Syntax_Syntax.pos)))
                      :: stack1 in
                    inline_closure_env cfg env1 stack2 head))
and (non_tail_inline_closure_env :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun cfg -> fun env1 -> fun t -> inline_closure_env cfg env1 [] t
and (rebuild_closure :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun t ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu___1 ->
               let uu___2 = FStar_Syntax_Print.tag_of_term t in
               let uu___3 = env_to_string env1 in
               let uu___4 = stack_to_string stack1 in
               let uu___5 = FStar_Syntax_Print.term_to_string t in
               FStar_Util.print4
                 ">>> %s (env=%s, stack=%s)\nRebuild closure_as_term %s\n"
                 uu___2 uu___3 uu___4 uu___5);
          (match stack1 with
           | [] -> t
           | (Arg (Clos (env_arg, tm, uu___1, uu___2), aq, r))::stack2 ->
               let stack3 = (App (env1, t, aq, r)) :: stack2 in
               inline_closure_env cfg env_arg stack3 tm
           | (App (env2, head, aq, r))::stack2 ->
               let t1 = FStar_Syntax_Syntax.extend_app head (t, aq) r in
               rebuild_closure cfg env2 stack2 t1
           | (CBVApp (env2, head, aq, r))::stack2 ->
               let t1 = FStar_Syntax_Syntax.extend_app head (t, aq) r in
               rebuild_closure cfg env2 stack2 t1
           | (Abs (env', bs, env'', lopt, r))::stack2 ->
               let uu___1 = close_binders cfg env' bs in
               (match uu___1 with
                | (bs1, uu___2) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt in
                    let uu___3 =
                      let uu___4 = FStar_Syntax_Util.abs bs1 t lopt1 in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___4.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___4.FStar_Syntax_Syntax.vars)
                      } in
                    rebuild_closure cfg env1 stack2 uu___3)
           | (Match (env2, asc_opt, branches1, cfg1, r))::stack2 ->
               let close_one_branch env3 uu___1 =
                 match uu___1 with
                 | (pat, w_opt, tm) ->
                     let rec norm_pat env4 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu___2 -> (p, env4)
                       | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
                           let uu___2 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu___3 ->
                                     fun uu___4 ->
                                       match (uu___3, uu___4) with
                                       | ((pats1, env5), (p1, b)) ->
                                           let uu___5 = norm_pat env5 p1 in
                                           (match uu___5 with
                                            | (p2, env6) ->
                                                (((p2, b) :: pats1), env6)))
                                  ([], env4)) in
                           (match uu___2 with
                            | (pats1, env5) ->
                                ((let uu___3 = p in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___3.FStar_Syntax_Syntax.p)
                                  }), env5))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___2 = x in
                             let uu___3 =
                               non_tail_inline_closure_env cfg1 env4
                                 x.FStar_Syntax_Syntax.sort in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu___3
                             } in
                           ((let uu___2 = p in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___2.FStar_Syntax_Syntax.p)
                             }), (dummy :: env4))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___2 = x in
                             let uu___3 =
                               non_tail_inline_closure_env cfg1 env4
                                 x.FStar_Syntax_Syntax.sort in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu___3
                             } in
                           ((let uu___2 = p in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___2.FStar_Syntax_Syntax.p)
                             }), (dummy :: env4))
                       | FStar_Syntax_Syntax.Pat_dot_term (x, t1) ->
                           let x1 =
                             let uu___2 = x in
                             let uu___3 =
                               non_tail_inline_closure_env cfg1 env4
                                 x.FStar_Syntax_Syntax.sort in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___2.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___2.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu___3
                             } in
                           let t2 = non_tail_inline_closure_env cfg1 env4 t1 in
                           ((let uu___2 = p in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___2.FStar_Syntax_Syntax.p)
                             }), env4) in
                     let uu___2 = norm_pat env3 pat in
                     (match uu___2 with
                      | (pat1, env4) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu___3 =
                                  non_tail_inline_closure_env cfg1 env4 w in
                                FStar_Pervasives_Native.Some uu___3 in
                          let tm1 = non_tail_inline_closure_env cfg1 env4 tm in
                          (pat1, w_opt1, tm1)) in
               let t1 =
                 let uu___1 =
                   let uu___2 =
                     let uu___3 =
                       FStar_Util.map_opt asc_opt
                         (close_ascription cfg1 env2) in
                     let uu___4 =
                       FStar_All.pipe_right branches1
                         (FStar_List.map (close_one_branch env2)) in
                     (t, uu___3, uu___4) in
                   FStar_Syntax_Syntax.Tm_match uu___2 in
                 FStar_Syntax_Syntax.mk uu___1 t.FStar_Syntax_Syntax.pos in
               rebuild_closure cfg1 env2 stack2 t1
           | (Meta (env_m, m, r))::stack2 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern (names, args) ->
                     let uu___1 =
                       let uu___2 =
                         FStar_All.pipe_right names
                           (FStar_List.map
                              (non_tail_inline_closure_env cfg env_m)) in
                       let uu___3 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun args1 ->
                                 FStar_All.pipe_right args1
                                   (FStar_List.map
                                      (fun uu___4 ->
                                         match uu___4 with
                                         | (a, q) ->
                                             let uu___5 =
                                               non_tail_inline_closure_env
                                                 cfg env_m a in
                                             (uu___5, q))))) in
                       (uu___2, uu___3) in
                     FStar_Syntax_Syntax.Meta_pattern uu___1
                 | FStar_Syntax_Syntax.Meta_monadic (m2, tbody) ->
                     let uu___1 =
                       let uu___2 =
                         non_tail_inline_closure_env cfg env_m tbody in
                       (m2, uu___2) in
                     FStar_Syntax_Syntax.Meta_monadic uu___1
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m11, m2, tbody) ->
                     let uu___1 =
                       let uu___2 =
                         non_tail_inline_closure_env cfg env_m tbody in
                       (m11, m2, uu___2) in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu___1
                 | uu___1 -> m in
               let t1 =
                 FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (t, m1))
                   r in
               rebuild_closure cfg env1 stack2 t1
           | uu___1 -> failwith "Impossible: unexpected stack element")
and (close_ascription :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
        FStar_Pervasives.either * FStar_Syntax_Syntax.term'
        FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option) ->
        ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
          FStar_Pervasives.either * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option))
  =
  fun cfg ->
    fun env1 ->
      fun uu___ ->
        match uu___ with
        | (annot, tacopt) ->
            let annot1 =
              match annot with
              | FStar_Pervasives.Inl t ->
                  let uu___1 = non_tail_inline_closure_env cfg env1 t in
                  FStar_Pervasives.Inl uu___1
              | FStar_Pervasives.Inr c ->
                  let uu___1 = close_comp cfg env1 c in
                  FStar_Pervasives.Inr uu___1 in
            let tacopt1 =
              FStar_Util.map_opt tacopt
                (non_tail_inline_closure_env cfg env1) in
            (annot1, tacopt1)
and (close_imp :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun cfg ->
    fun env1 ->
      fun imp ->
        match imp with
        | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
            let uu___ =
              let uu___1 = inline_closure_env cfg env1 [] t in
              FStar_Syntax_Syntax.Meta uu___1 in
            FStar_Pervasives_Native.Some uu___
        | i -> i
and (close_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.binder Prims.list ->
        (FStar_Syntax_Syntax.binder Prims.list * env))
  =
  fun cfg ->
    fun env1 ->
      fun bs ->
        let uu___ =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu___1 ->
                  fun uu___2 ->
                    match (uu___1, uu___2) with
                    | ((env2, out),
                       { FStar_Syntax_Syntax.binder_bv = b;
                         FStar_Syntax_Syntax.binder_qual = imp;
                         FStar_Syntax_Syntax.binder_attrs = attrs;_})
                        ->
                        let b1 =
                          let uu___3 = b in
                          let uu___4 =
                            inline_closure_env cfg env2 []
                              b.FStar_Syntax_Syntax.sort in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu___4
                          } in
                        let imp1 = close_imp cfg env2 imp in
                        let attrs1 =
                          FStar_List.map
                            (non_tail_inline_closure_env cfg env2) attrs in
                        let env3 = dummy :: env2 in
                        let uu___3 =
                          let uu___4 =
                            FStar_Syntax_Syntax.mk_binder_with_attrs b1 imp1
                              attrs1 in
                          uu___4 :: out in
                        (env3, uu___3)) (env1, [])) in
        match uu___ with | (env2, bs1) -> ((FStar_List.rev bs1), env2)
and (close_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun cfg ->
    fun env1 ->
      fun c ->
        match env1 with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
            -> c
        | uu___ ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t, uopt) ->
                 let uu___1 = inline_closure_env cfg env1 [] t in
                 let uu___2 = FStar_Option.map (norm_universe cfg env1) uopt in
                 FStar_Syntax_Syntax.mk_Total' uu___1 uu___2
             | FStar_Syntax_Syntax.GTotal (t, uopt) ->
                 let uu___1 = inline_closure_env cfg env1 [] t in
                 let uu___2 = FStar_Option.map (norm_universe cfg env1) uopt in
                 FStar_Syntax_Syntax.mk_GTotal' uu___1 uu___2
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env1 []
                     c1.FStar_Syntax_Syntax.result_typ in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu___1 ->
                           match uu___1 with
                           | (a, q) ->
                               let uu___2 = inline_closure_env cfg env1 [] a in
                               (uu___2, q))) in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___1 ->
                           match uu___1 with
                           | FStar_Syntax_Syntax.DECREASES
                               (FStar_Syntax_Syntax.Decreases_lex l) ->
                               let uu___2 =
                                 let uu___3 =
                                   FStar_All.pipe_right l
                                     (FStar_List.map
                                        (inline_closure_env cfg env1 [])) in
                                 FStar_All.pipe_right uu___3
                                   (fun uu___4 ->
                                      FStar_Syntax_Syntax.Decreases_lex
                                        uu___4) in
                               FStar_Syntax_Syntax.DECREASES uu___2
                           | FStar_Syntax_Syntax.DECREASES
                               (FStar_Syntax_Syntax.Decreases_wf (rel, e)) ->
                               let uu___2 =
                                 let uu___3 =
                                   let uu___4 =
                                     inline_closure_env cfg env1 [] rel in
                                   let uu___5 =
                                     inline_closure_env cfg env1 [] e in
                                   (uu___4, uu___5) in
                                 FStar_Syntax_Syntax.Decreases_wf uu___3 in
                               FStar_Syntax_Syntax.DECREASES uu___2
                           | f -> f)) in
                 let uu___1 =
                   let uu___2 = c1 in
                   let uu___3 =
                     FStar_List.map (norm_universe cfg env1)
                       c1.FStar_Syntax_Syntax.comp_univs in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu___3;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___2.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   } in
                 FStar_Syntax_Syntax.mk_Comp uu___1)
and (close_lcomp_opt :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun cfg ->
    fun env1 ->
      fun lopt ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___ ->
                      match uu___ with
                      | FStar_Syntax_Syntax.DECREASES uu___1 -> false
                      | uu___1 -> true)) in
            let rc1 =
              let uu___ = rc in
              let uu___1 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env1 []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu___1;
                FStar_Syntax_Syntax.residual_flags = flags
              } in
            FStar_Pervasives_Native.Some rc1
        | uu___ -> lopt
let (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___ ->
            match uu___ with
            | FStar_Syntax_Syntax.DECREASES uu___1 -> false
            | uu___1 -> true))
let (closure_as_term :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun cfg -> fun env1 -> fun t -> non_tail_inline_closure_env cfg env1 t
let (unembed_binder_knot :
  FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ = FStar_ST.op_Bang unembed_binder_knot in
    match uu___ with
    | FStar_Pervasives_Native.Some e ->
        let uu___1 = FStar_Syntax_Embeddings.unembed e t in
        uu___1 false FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
let (mk_psc_subst :
  FStar_TypeChecker_Cfg.cfg ->
    (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
      Prims.list -> FStar_Syntax_Syntax.subst_elt Prims.list)
  =
  fun cfg ->
    fun env1 ->
      FStar_List.fold_right
        (fun uu___ ->
           fun subst ->
             match uu___ with
             | (binder_opt, closure1) ->
                 (match (binder_opt, closure1) with
                  | (FStar_Pervasives_Native.Some b, Clos
                     (env2, term, uu___1, uu___2)) ->
                      let bv = b.FStar_Syntax_Syntax.binder_bv in
                      let uu___3 =
                        let uu___4 =
                          FStar_Syntax_Util.is_constructed_typ
                            bv.FStar_Syntax_Syntax.sort
                            FStar_Parser_Const.binder_lid in
                        Prims.op_Negation uu___4 in
                      if uu___3
                      then subst
                      else
                        (let term1 = closure_as_term cfg env2 term in
                         let uu___5 = unembed_binder term1 in
                         match uu___5 with
                         | FStar_Pervasives_Native.None -> subst
                         | FStar_Pervasives_Native.Some x ->
                             let b1 =
                               let uu___6 =
                                 let uu___7 = bv in
                                 let uu___8 =
                                   FStar_Syntax_Subst.subst subst
                                     (x.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___7.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___7.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu___8
                                 } in
                               FStar_Syntax_Syntax.freshen_bv uu___6 in
                             let b_for_x =
                               let uu___6 =
                                 let uu___7 =
                                   FStar_Syntax_Syntax.bv_to_name b1 in
                                 ((x.FStar_Syntax_Syntax.binder_bv), uu___7) in
                               FStar_Syntax_Syntax.NT uu___6 in
                             let subst1 =
                               FStar_List.filter
                                 (fun uu___6 ->
                                    match uu___6 with
                                    | FStar_Syntax_Syntax.NT
                                        (uu___7,
                                         {
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_name b';
                                           FStar_Syntax_Syntax.pos = uu___8;
                                           FStar_Syntax_Syntax.vars = uu___9;_})
                                        ->
                                        let uu___10 =
                                          FStar_Ident.ident_equals
                                            b1.FStar_Syntax_Syntax.ppname
                                            b'.FStar_Syntax_Syntax.ppname in
                                        Prims.op_Negation uu___10
                                    | uu___7 -> true) subst in
                             b_for_x :: subst1)
                  | uu___1 -> subst)) env1 []
let (reduce_primops :
  FStar_Syntax_Embeddings.norm_cb ->
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
        Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun norm_cb ->
    fun cfg ->
      fun env1 ->
        fun tm ->
          if
            Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
          then tm
          else
            (let uu___1 = FStar_Syntax_Util.head_and_args tm in
             match uu___1 with
             | (head, args) ->
                 let uu___2 =
                   let uu___3 = FStar_Syntax_Util.un_uinst head in
                   uu___3.FStar_Syntax_Syntax.n in
                 (match uu___2 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu___3 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv in
                      (match uu___3 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok
                             ||
                             (Prims.op_Negation
                                cfg.FStar_TypeChecker_Cfg.strong)
                           ->
                           let l = FStar_List.length args in
                           if l < prim_step.FStar_TypeChecker_Cfg.arity
                           then
                             (FStar_TypeChecker_Cfg.log_primops cfg
                                (fun uu___5 ->
                                   let uu___6 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name in
                                   let uu___7 = FStar_Util.string_of_int l in
                                   let uu___8 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu___6 uu___7 uu___8);
                              tm)
                           else
                             (let uu___5 =
                                if l = prim_step.FStar_TypeChecker_Cfg.arity
                                then (args, [])
                                else
                                  FStar_List.splitAt
                                    prim_step.FStar_TypeChecker_Cfg.arity
                                    args in
                              match uu___5 with
                              | (args_1, args_2) ->
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu___7 ->
                                        let uu___8 =
                                          FStar_Syntax_Print.term_to_string
                                            tm in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu___8);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu___7 ->
                                             if
                                               prim_step.FStar_TypeChecker_Cfg.requires_binder_substitution
                                             then mk_psc_subst cfg env1
                                             else [])
                                      } in
                                    let r =
                                      prim_step.FStar_TypeChecker_Cfg.interpretation
                                        psc norm_cb args_1 in
                                    match r with
                                    | FStar_Pervasives_Native.None ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu___8 ->
                                              let uu___9 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu___9);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu___8 ->
                                              let uu___9 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm in
                                              let uu___10 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu___9 uu___10);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu___4 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu___6 ->
                                 let uu___7 =
                                   FStar_Syntax_Print.term_to_string tm in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu___7);
                            tm)
                       | FStar_Pervasives_Native.None -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu___4 ->
                            let uu___5 = FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu___5);
                       (match args with
                        | (a1, uu___4)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu___4 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu___4 ->
                            let uu___5 = FStar_Syntax_Print.term_to_string tm in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu___5);
                       (match args with
                        | (t, uu___4)::(r, uu___5)::[] ->
                            let uu___6 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r in
                            (match uu___6 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None -> tm)
                        | uu___4 -> tm))
                  | uu___3 -> tm))
let (reduce_equality :
  FStar_Syntax_Embeddings.norm_cb ->
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
        Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun norm_cb ->
    fun cfg ->
      fun tm ->
        reduce_primops norm_cb
          (let uu___ = cfg in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___1 = FStar_TypeChecker_Cfg.default_steps in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___1.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___1.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___1.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.zeta_full =
                    (uu___1.FStar_TypeChecker_Cfg.zeta_full);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___1.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___1.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___1.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___1.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___1.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___1.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___1.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_qual =
                    (uu___1.FStar_TypeChecker_Cfg.unfold_qual);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___1.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___1.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___1.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___1.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___1.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___1.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___1.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___1.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___1.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___1.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___1.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___1.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___1.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___1.FStar_TypeChecker_Cfg.nbe_step);
                  FStar_TypeChecker_Cfg.for_extraction =
                    (uu___1.FStar_TypeChecker_Cfg.for_extraction)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___.FStar_TypeChecker_Cfg.reifying)
           }) tm
type norm_request_t =
  | Norm_request_none 
  | Norm_request_ready 
  | Norm_request_requires_rejig 
let (uu___is_Norm_request_none : norm_request_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Norm_request_none -> true | uu___ -> false
let (uu___is_Norm_request_ready : norm_request_t -> Prims.bool) =
  fun projectee ->
    match projectee with | Norm_request_ready -> true | uu___ -> false
let (uu___is_Norm_request_requires_rejig : norm_request_t -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Norm_request_requires_rejig -> true
    | uu___ -> false
let (is_norm_request :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.args -> norm_request_t) =
  fun hd ->
    fun args ->
      let aux min_args =
        let uu___ = FStar_All.pipe_right args FStar_List.length in
        FStar_All.pipe_right uu___
          (fun n ->
             if n < min_args
             then Norm_request_none
             else
               if n = min_args
               then Norm_request_ready
               else Norm_request_requires_rejig) in
      let uu___ =
        let uu___1 = FStar_Syntax_Util.un_uinst hd in
        uu___1.FStar_Syntax_Syntax.n in
      match uu___ with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          -> aux (Prims.of_int (2))
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          aux Prims.int_one
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          aux (Prims.of_int (3))
      | uu___1 -> Norm_request_none
let (should_consider_norm_requests : FStar_TypeChecker_Cfg.cfg -> Prims.bool)
  =
  fun cfg ->
    (Prims.op_Negation
       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
      &&
      (let uu___ =
         FStar_Ident.lid_equals
           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
           FStar_Parser_Const.prims_lid in
       Prims.op_Negation uu___)
let (rejig_norm_request :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term)
  =
  fun hd ->
    fun args ->
      let uu___ =
        let uu___1 = FStar_Syntax_Util.un_uinst hd in
        uu___1.FStar_Syntax_Syntax.n in
      match uu___ with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          ->
          (match args with
           | t1::t2::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu___1 = FStar_Syntax_Util.mk_app hd [t1; t2] in
               FStar_Syntax_Util.mk_app uu___1 rest
           | uu___1 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize_term")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          (match args with
           | t::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu___1 = FStar_Syntax_Util.mk_app hd [t] in
               FStar_Syntax_Util.mk_app uu___1 rest
           | uu___1 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          (match args with
           | t1::t2::t3::rest when (FStar_List.length rest) > Prims.int_zero
               ->
               let uu___1 = FStar_Syntax_Util.mk_app hd [t1; t2; t3] in
               FStar_Syntax_Util.mk_app uu___1 rest
           | uu___1 ->
               failwith "Impossible! invalid rejig_norm_request for norm")
      | uu___1 ->
          let uu___2 =
            let uu___3 = FStar_Syntax_Print.term_to_string hd in
            FStar_String.op_Hat
              "Impossible! invalid rejig_norm_request for: %s" uu___3 in
          failwith uu___2
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Syntax_Embeddings.Zeta -> [FStar_TypeChecker_Env.Zeta]
    | FStar_Syntax_Embeddings.ZetaFull -> [FStar_TypeChecker_Env.ZetaFull]
    | FStar_Syntax_Embeddings.Iota -> [FStar_TypeChecker_Env.Iota]
    | FStar_Syntax_Embeddings.Delta ->
        [FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl -> [FStar_TypeChecker_Env.Simplify]
    | FStar_Syntax_Embeddings.Weak -> [FStar_TypeChecker_Env.Weak]
    | FStar_Syntax_Embeddings.HNF -> [FStar_TypeChecker_Env.HNF]
    | FStar_Syntax_Embeddings.Primops -> [FStar_TypeChecker_Env.Primops]
    | FStar_Syntax_Embeddings.Reify -> [FStar_TypeChecker_Env.Reify]
    | FStar_Syntax_Embeddings.UnfoldOnly names ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_List.map FStar_Ident.lid_of_str names in
            FStar_TypeChecker_Env.UnfoldOnly uu___3 in
          [uu___2] in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu___1
    | FStar_Syntax_Embeddings.UnfoldFully names ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_List.map FStar_Ident.lid_of_str names in
            FStar_TypeChecker_Env.UnfoldFully uu___3 in
          [uu___2] in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu___1
    | FStar_Syntax_Embeddings.UnfoldAttr names ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_List.map FStar_Ident.lid_of_str names in
            FStar_TypeChecker_Env.UnfoldAttr uu___3 in
          [uu___2] in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu___1
    | FStar_Syntax_Embeddings.UnfoldQual names ->
        [FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.UnfoldQual names]
    | FStar_Syntax_Embeddings.NBE -> [FStar_TypeChecker_Env.NBE]
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  =
  fun s ->
    let s1 = FStar_List.concatMap tr_norm_step s in
    let add_exclude s2 z =
      let uu___ = FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s2 in
      if uu___ then s2 else (FStar_TypeChecker_Env.Exclude z) :: s2 in
    let s2 = FStar_TypeChecker_Env.Beta :: s1 in
    let s3 = add_exclude s2 FStar_TypeChecker_Env.Zeta in
    let s4 = add_exclude s3 FStar_TypeChecker_Env.Iota in s4
let get_norm_request :
  'uuuuu .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term * 'uuuuu) Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list * FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.option
  =
  fun cfg ->
    fun full_norm ->
      fun args ->
        let parse_steps s =
          let uu___ =
            let uu___1 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step in
            FStar_TypeChecker_Cfg.try_unembed_simple uu___1 s in
          match uu___ with
          | FStar_Pervasives_Native.Some steps ->
              let uu___1 = tr_norm_steps steps in
              FStar_Pervasives_Native.Some uu___1
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
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
                else [])) in
        match args with
        | uu___::(tm, uu___1)::[] ->
            let s =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.Iota;
              FStar_TypeChecker_Env.Primops;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant;
              FStar_TypeChecker_Env.Reify] in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (tm, uu___)::[] ->
            let s =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.Iota;
              FStar_TypeChecker_Env.Primops;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant;
              FStar_TypeChecker_Env.Reify] in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (steps, uu___)::uu___1::(tm, uu___2)::[] ->
            let uu___3 = let uu___4 = full_norm steps in parse_steps uu___4 in
            (match uu___3 with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s), tm))
        | uu___ -> FStar_Pervasives_Native.None
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun s ->
      fun tm ->
        let delta_level =
          let uu___ =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___1 ->
                    match uu___1 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu___2 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu___2 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu___2 -> true
                    | uu___2 -> false)) in
          if uu___
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta] in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu___1 ->
             let uu___2 = FStar_Syntax_Print.term_to_string tm in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu___2);
        (let tm_norm =
           let uu___1 = FStar_TypeChecker_Cfg.cfg_env cfg in
           uu___1.FStar_TypeChecker_Env.nbe s cfg.FStar_TypeChecker_Cfg.tcenv
             tm in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu___2 ->
              let uu___3 = FStar_Syntax_Print.term_to_string tm_norm in
              FStar_Util.print1 "Result of NBE is  %s\n" uu___3);
         tm_norm)
let firstn :
  'uuuuu .
    Prims.int -> 'uuuuu Prims.list -> ('uuuuu Prims.list * 'uuuuu Prims.list)
  =
  fun k ->
    fun l ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg ->
    fun stack1 ->
      let rec drop_irrel uu___ =
        match uu___ with
        | (MemoLazy uu___1)::s -> drop_irrel s
        | (UnivArgs uu___1)::s -> drop_irrel s
        | s -> s in
      let uu___ = drop_irrel stack1 in
      match uu___ with
      | (App
          (uu___1,
           {
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_reify);
             FStar_Syntax_Syntax.pos = uu___2;
             FStar_Syntax_Syntax.vars = uu___3;_},
           uu___4, uu___5))::uu___6
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu___1 -> false
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t, uu___) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t, uu___) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu___ ->
                  match uu___ with | (a, uu___1) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args) in
    let t = FStar_Syntax_Subst.compress tm in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu___ -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu___ -> false
    | FStar_Syntax_Syntax.Tm_uvar uu___ -> false
    | FStar_Syntax_Syntax.Tm_type uu___ -> false
    | FStar_Syntax_Syntax.Tm_bvar uu___ -> false
    | FStar_Syntax_Syntax.Tm_fvar uu___ -> false
    | FStar_Syntax_Syntax.Tm_constant uu___ -> false
    | FStar_Syntax_Syntax.Tm_lazy uu___ -> false
    | FStar_Syntax_Syntax.Tm_unknown -> false
    | FStar_Syntax_Syntax.Tm_uinst uu___ -> false
    | FStar_Syntax_Syntax.Tm_quoted uu___ -> false
    | FStar_Syntax_Syntax.Tm_let uu___ -> true
    | FStar_Syntax_Syntax.Tm_abs uu___ -> true
    | FStar_Syntax_Syntax.Tm_arrow uu___ -> true
    | FStar_Syntax_Syntax.Tm_refine uu___ -> true
    | FStar_Syntax_Syntax.Tm_match uu___ -> true
    | FStar_Syntax_Syntax.Tm_app (t1, args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu___ ->
                   match uu___ with | (a, uu___1) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu___) ->
        ((maybe_weakly_reduced t1) ||
           (match FStar_Pervasives_Native.fst asc with
            | FStar_Pervasives.Inl t2 -> maybe_weakly_reduced t2
            | FStar_Pervasives.Inr c2 -> aux_comp c2))
          ||
          ((match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None -> false
            | FStar_Pervasives_Native.Some tac -> maybe_weakly_reduced tac))
    | FStar_Syntax_Syntax.Tm_meta (t1, m) ->
        (maybe_weakly_reduced t1) ||
          ((match m with
            | FStar_Syntax_Syntax.Meta_pattern (uu___, args) ->
                FStar_Util.for_some
                  (FStar_Util.for_some
                     (fun uu___1 ->
                        match uu___1 with
                        | (a, uu___2) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift (uu___, uu___1, t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu___, t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu___ -> false
            | FStar_Syntax_Syntax.Meta_desugared uu___ -> false
            | FStar_Syntax_Syntax.Meta_named uu___ -> false))
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee ->
    match projectee with | Should_unfold_no -> true | uu___ -> false
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee ->
    match projectee with | Should_unfold_yes -> true | uu___ -> false
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee ->
    match projectee with | Should_unfold_fully -> true | uu___ -> false
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee ->
    match projectee with | Should_unfold_reify -> true | uu___ -> false
let (plugin_unfold_warn_ctr : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref Prims.int_zero
let (should_unfold :
  FStar_TypeChecker_Cfg.cfg ->
    (FStar_TypeChecker_Cfg.cfg -> Prims.bool) ->
      FStar_Syntax_Syntax.fv ->
        FStar_TypeChecker_Env.qninfo -> should_unfold_res)
  =
  fun cfg ->
    fun should_reify1 ->
      fun fv ->
        fun qninfo ->
          let attrs =
            let uu___ = FStar_TypeChecker_Env.attrs_of_qninfo qninfo in
            match uu___ with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some ats -> ats in
          let quals =
            let uu___ = FStar_TypeChecker_Env.quals_of_qninfo qninfo in
            match uu___ with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some quals1 -> quals1 in
          let yes = (true, false, false) in
          let no = (false, false, false) in
          let fully = (true, true, false) in
          let reif = (true, false, true) in
          let yesno b = if b then yes else no in
          let fullyno b = if b then fully else no in
          let comb_or l =
            FStar_List.fold_right
              (fun uu___ ->
                 fun uu___1 ->
                   match (uu___, uu___1) with
                   | ((a, b, c), (x, y, z)) -> ((a || x), (b || y), (c || z)))
              l (false, false, false) in
          let string_of_res uu___ =
            match uu___ with
            | (x, y, z) ->
                let uu___1 = FStar_Util.string_of_bool x in
                let uu___2 = FStar_Util.string_of_bool y in
                let uu___3 = FStar_Util.string_of_bool z in
                FStar_Util.format3 "(%s,%s,%s)" uu___1 uu___2 uu___3 in
          let default_unfolding uu___ =
            FStar_TypeChecker_Cfg.log_unfolding cfg
              (fun uu___2 ->
                 let uu___3 = FStar_Syntax_Print.fv_to_string fv in
                 let uu___4 =
                   FStar_Syntax_Print.delta_depth_to_string
                     fv.FStar_Syntax_Syntax.fv_delta in
                 let uu___5 =
                   FStar_Common.string_of_list
                     FStar_TypeChecker_Env.string_of_delta_level
                     cfg.FStar_TypeChecker_Cfg.delta_level in
                 FStar_Util.print3
                   "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                   uu___3 uu___4 uu___5);
            (let uu___2 =
               FStar_All.pipe_right cfg.FStar_TypeChecker_Cfg.delta_level
                 (FStar_Util.for_some
                    (fun uu___3 ->
                       match uu___3 with
                       | FStar_TypeChecker_Env.NoDelta -> false
                       | FStar_TypeChecker_Env.InliningDelta -> true
                       | FStar_TypeChecker_Env.Eager_unfolding_only -> true
                       | FStar_TypeChecker_Env.Unfold l ->
                           let uu___4 =
                             FStar_TypeChecker_Env.delta_depth_of_fv
                               cfg.FStar_TypeChecker_Cfg.tcenv fv in
                           FStar_TypeChecker_Common.delta_depth_greater_than
                             uu___4 l)) in
             FStar_All.pipe_left yesno uu___2) in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu___1 ->
                    let uu___2 = FStar_Syntax_Print.fv_to_string fv in
                    let uu___3 = FStar_Util.string_of_bool b in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu___2 uu___3);
               if b then reif else no)
            else
              if
                (let uu___ = FStar_TypeChecker_Cfg.find_prim_step cfg fv in
                 FStar_Option.isSome uu___)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu___1 ->
                      FStar_Util.print_string
                        " >> It's a primop, not unfolding\n");
                 no)
              else
                (match (qninfo,
                         ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only),
                         ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully),
                         ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr),
                         ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_qual))
                 with
                 | (FStar_Pervasives_Native.Some
                    (FStar_Pervasives.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec, uu___), uu___1);
                        FStar_Syntax_Syntax.sigrng = uu___2;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu___3;
                        FStar_Syntax_Syntax.sigattrs = uu___4;
                        FStar_Syntax_Syntax.sigopts = uu___5;_},
                      uu___6),
                     uu___7),
                    uu___8, uu___9, uu___10, uu___11) when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu___13 ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu___, uu___1, uu___2, uu___3, uu___4) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu___6 ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Pervasives.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec, uu___), uu___1);
                        FStar_Syntax_Syntax.sigrng = uu___2;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu___3;
                        FStar_Syntax_Syntax.sigattrs = uu___4;
                        FStar_Syntax_Syntax.sigopts = uu___5;_},
                      uu___6),
                     uu___7),
                    uu___8, uu___9, uu___10, uu___11) when
                     (is_rec &&
                        (Prims.op_Negation
                           (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta))
                       &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu___13 ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu___, FStar_Pervasives_Native.Some uu___1, uu___2,
                    uu___3, uu___4) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu___6 ->
                           let uu___7 = FStar_Syntax_Print.fv_to_string fv in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu___7);
                      (let meets_some_criterion =
                         let uu___6 =
                           let uu___7 =
                             if
                               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                             then
                               let uu___8 =
                                 let uu___9 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     [FStar_TypeChecker_Env.Eager_unfolding_only;
                                     FStar_TypeChecker_Env.InliningDelta]
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo in
                                 FStar_Option.isSome uu___9 in
                               FStar_All.pipe_left yesno uu___8
                             else no in
                           let uu___8 =
                             let uu___9 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                               with
                               | FStar_Pervasives_Native.None -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu___10 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids in
                                   FStar_All.pipe_left yesno uu___10 in
                             let uu___10 =
                               let uu___11 =
                                 match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                                 with
                                 | FStar_Pervasives_Native.None -> no
                                 | FStar_Pervasives_Native.Some lids ->
                                     let uu___12 =
                                       FStar_Util.for_some
                                         (fun at ->
                                            FStar_Util.for_some
                                              (fun lid ->
                                                 FStar_Syntax_Util.is_fvar
                                                   lid at) lids) attrs in
                                     FStar_All.pipe_left yesno uu___12 in
                               let uu___12 =
                                 let uu___13 =
                                   match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                                   with
                                   | FStar_Pervasives_Native.None -> no
                                   | FStar_Pervasives_Native.Some lids ->
                                       let uu___14 =
                                         FStar_Util.for_some
                                           (FStar_Syntax_Syntax.fv_eq_lid fv)
                                           lids in
                                       FStar_All.pipe_left fullyno uu___14 in
                                 let uu___14 =
                                   let uu___15 =
                                     match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_qual
                                     with
                                     | FStar_Pervasives_Native.None -> no
                                     | FStar_Pervasives_Native.Some qs ->
                                         let uu___16 =
                                           FStar_Util.for_some
                                             (fun q ->
                                                FStar_Util.for_some
                                                  (fun qual ->
                                                     let uu___17 =
                                                       FStar_Syntax_Print.qual_to_string
                                                         qual in
                                                     uu___17 = q) quals) qs in
                                         FStar_All.pipe_left yesno uu___16 in
                                   [uu___15] in
                                 uu___13 :: uu___14 in
                               uu___11 :: uu___12 in
                             uu___9 :: uu___10 in
                           uu___7 :: uu___8 in
                         comb_or uu___6 in
                       meets_some_criterion))
                 | (uu___, uu___1, FStar_Pervasives_Native.Some uu___2,
                    uu___3, uu___4) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu___6 ->
                           let uu___7 = FStar_Syntax_Print.fv_to_string fv in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu___7);
                      (let meets_some_criterion =
                         let uu___6 =
                           let uu___7 =
                             if
                               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                             then
                               let uu___8 =
                                 let uu___9 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     [FStar_TypeChecker_Env.Eager_unfolding_only;
                                     FStar_TypeChecker_Env.InliningDelta]
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo in
                                 FStar_Option.isSome uu___9 in
                               FStar_All.pipe_left yesno uu___8
                             else no in
                           let uu___8 =
                             let uu___9 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                               with
                               | FStar_Pervasives_Native.None -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu___10 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids in
                                   FStar_All.pipe_left yesno uu___10 in
                             let uu___10 =
                               let uu___11 =
                                 match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                                 with
                                 | FStar_Pervasives_Native.None -> no
                                 | FStar_Pervasives_Native.Some lids ->
                                     let uu___12 =
                                       FStar_Util.for_some
                                         (fun at ->
                                            FStar_Util.for_some
                                              (fun lid ->
                                                 FStar_Syntax_Util.is_fvar
                                                   lid at) lids) attrs in
                                     FStar_All.pipe_left yesno uu___12 in
                               let uu___12 =
                                 let uu___13 =
                                   match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                                   with
                                   | FStar_Pervasives_Native.None -> no
                                   | FStar_Pervasives_Native.Some lids ->
                                       let uu___14 =
                                         FStar_Util.for_some
                                           (FStar_Syntax_Syntax.fv_eq_lid fv)
                                           lids in
                                       FStar_All.pipe_left fullyno uu___14 in
                                 let uu___14 =
                                   let uu___15 =
                                     match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_qual
                                     with
                                     | FStar_Pervasives_Native.None -> no
                                     | FStar_Pervasives_Native.Some qs ->
                                         let uu___16 =
                                           FStar_Util.for_some
                                             (fun q ->
                                                FStar_Util.for_some
                                                  (fun qual ->
                                                     let uu___17 =
                                                       FStar_Syntax_Print.qual_to_string
                                                         qual in
                                                     uu___17 = q) quals) qs in
                                         FStar_All.pipe_left yesno uu___16 in
                                   [uu___15] in
                                 uu___13 :: uu___14 in
                               uu___11 :: uu___12 in
                             uu___9 :: uu___10 in
                           uu___7 :: uu___8 in
                         comb_or uu___6 in
                       meets_some_criterion))
                 | (uu___, uu___1, uu___2, FStar_Pervasives_Native.Some
                    uu___3, uu___4) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu___6 ->
                           let uu___7 = FStar_Syntax_Print.fv_to_string fv in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu___7);
                      (let meets_some_criterion =
                         let uu___6 =
                           let uu___7 =
                             if
                               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                             then
                               let uu___8 =
                                 let uu___9 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     [FStar_TypeChecker_Env.Eager_unfolding_only;
                                     FStar_TypeChecker_Env.InliningDelta]
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo in
                                 FStar_Option.isSome uu___9 in
                               FStar_All.pipe_left yesno uu___8
                             else no in
                           let uu___8 =
                             let uu___9 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                               with
                               | FStar_Pervasives_Native.None -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu___10 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids in
                                   FStar_All.pipe_left yesno uu___10 in
                             let uu___10 =
                               let uu___11 =
                                 match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                                 with
                                 | FStar_Pervasives_Native.None -> no
                                 | FStar_Pervasives_Native.Some lids ->
                                     let uu___12 =
                                       FStar_Util.for_some
                                         (fun at ->
                                            FStar_Util.for_some
                                              (fun lid ->
                                                 FStar_Syntax_Util.is_fvar
                                                   lid at) lids) attrs in
                                     FStar_All.pipe_left yesno uu___12 in
                               let uu___12 =
                                 let uu___13 =
                                   match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                                   with
                                   | FStar_Pervasives_Native.None -> no
                                   | FStar_Pervasives_Native.Some lids ->
                                       let uu___14 =
                                         FStar_Util.for_some
                                           (FStar_Syntax_Syntax.fv_eq_lid fv)
                                           lids in
                                       FStar_All.pipe_left fullyno uu___14 in
                                 let uu___14 =
                                   let uu___15 =
                                     match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_qual
                                     with
                                     | FStar_Pervasives_Native.None -> no
                                     | FStar_Pervasives_Native.Some qs ->
                                         let uu___16 =
                                           FStar_Util.for_some
                                             (fun q ->
                                                FStar_Util.for_some
                                                  (fun qual ->
                                                     let uu___17 =
                                                       FStar_Syntax_Print.qual_to_string
                                                         qual in
                                                     uu___17 = q) quals) qs in
                                         FStar_All.pipe_left yesno uu___16 in
                                   [uu___15] in
                                 uu___13 :: uu___14 in
                               uu___11 :: uu___12 in
                             uu___9 :: uu___10 in
                           uu___7 :: uu___8 in
                         comb_or uu___6 in
                       meets_some_criterion))
                 | (uu___, uu___1, uu___2, uu___3,
                    FStar_Pervasives_Native.Some uu___4) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu___6 ->
                           let uu___7 = FStar_Syntax_Print.fv_to_string fv in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu___7);
                      (let meets_some_criterion =
                         let uu___6 =
                           let uu___7 =
                             if
                               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                             then
                               let uu___8 =
                                 let uu___9 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     [FStar_TypeChecker_Env.Eager_unfolding_only;
                                     FStar_TypeChecker_Env.InliningDelta]
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo in
                                 FStar_Option.isSome uu___9 in
                               FStar_All.pipe_left yesno uu___8
                             else no in
                           let uu___8 =
                             let uu___9 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                               with
                               | FStar_Pervasives_Native.None -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu___10 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids in
                                   FStar_All.pipe_left yesno uu___10 in
                             let uu___10 =
                               let uu___11 =
                                 match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                                 with
                                 | FStar_Pervasives_Native.None -> no
                                 | FStar_Pervasives_Native.Some lids ->
                                     let uu___12 =
                                       FStar_Util.for_some
                                         (fun at ->
                                            FStar_Util.for_some
                                              (fun lid ->
                                                 FStar_Syntax_Util.is_fvar
                                                   lid at) lids) attrs in
                                     FStar_All.pipe_left yesno uu___12 in
                               let uu___12 =
                                 let uu___13 =
                                   match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                                   with
                                   | FStar_Pervasives_Native.None -> no
                                   | FStar_Pervasives_Native.Some lids ->
                                       let uu___14 =
                                         FStar_Util.for_some
                                           (FStar_Syntax_Syntax.fv_eq_lid fv)
                                           lids in
                                       FStar_All.pipe_left fullyno uu___14 in
                                 let uu___14 =
                                   let uu___15 =
                                     match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_qual
                                     with
                                     | FStar_Pervasives_Native.None -> no
                                     | FStar_Pervasives_Native.Some qs ->
                                         let uu___16 =
                                           FStar_Util.for_some
                                             (fun q ->
                                                FStar_Util.for_some
                                                  (fun qual ->
                                                     let uu___17 =
                                                       FStar_Syntax_Print.qual_to_string
                                                         qual in
                                                     uu___17 = q) quals) qs in
                                         FStar_All.pipe_left yesno uu___16 in
                                   [uu___15] in
                                 uu___13 :: uu___14 in
                               uu___11 :: uu___12 in
                             uu___9 :: uu___10 in
                           uu___7 :: uu___8 in
                         comb_or uu___6 in
                       meets_some_criterion))
                 | uu___ -> default_unfolding ()) in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu___1 ->
               let uu___2 = FStar_Syntax_Print.fv_to_string fv in
               let uu___3 =
                 let uu___4 = FStar_Syntax_Syntax.range_of_fv fv in
                 FStar_Range.string_of_range uu___4 in
               let uu___4 = string_of_res res in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n" uu___2
                 uu___3 uu___4);
          (let r =
             match res with
             | (false, uu___1, uu___2) -> Should_unfold_no
             | (true, false, false) -> Should_unfold_yes
             | (true, true, false) -> Should_unfold_fully
             | (true, false, true) -> Should_unfold_reify
             | uu___1 ->
                 let uu___2 =
                   let uu___3 = string_of_res res in
                   FStar_Util.format1 "Unexpected unfolding result: %s"
                     uu___3 in
                 FStar_All.pipe_left failwith uu___2 in
           (let uu___2 =
              (((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                  && (r <> Should_unfold_no))
                 &&
                 (FStar_Util.for_some
                    (FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr)
                    attrs))
                &&
                (let uu___3 = FStar_ST.op_Bang plugin_unfold_warn_ctr in
                 uu___3 > Prims.int_zero) in
            if uu___2
            then
              ((let uu___4 =
                  let uu___5 =
                    let uu___6 = FStar_Syntax_Print.fv_to_string fv in
                    FStar_Util.format1
                      "Unfolding name which is marked as a plugin: %s" uu___6 in
                  (FStar_Errors.Warning_UnfoldPlugin, uu___5) in
                FStar_Errors.log_issue
                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                  uu___4);
               (let uu___4 =
                  let uu___5 = FStar_ST.op_Bang plugin_unfold_warn_ctr in
                  uu___5 - Prims.int_one in
                FStar_ST.op_Colon_Equals plugin_unfold_warn_ctr uu___4))
            else ());
           r)
let decide_unfolding :
  'uuuuu .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'uuuuu ->
            FStar_Syntax_Syntax.fv ->
              FStar_TypeChecker_Env.qninfo ->
                (FStar_TypeChecker_Cfg.cfg * stack_elt Prims.list)
                  FStar_Pervasives_Native.option
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun rng ->
          fun fv ->
            fun qninfo ->
              let res =
                should_unfold cfg (fun cfg1 -> should_reify cfg1 stack1) fv
                  qninfo in
              match res with
              | Should_unfold_no -> FStar_Pervasives_Native.None
              | Should_unfold_yes ->
                  FStar_Pervasives_Native.Some (cfg, stack1)
              | Should_unfold_fully ->
                  let cfg' =
                    let uu___ = cfg in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___1 = cfg.FStar_TypeChecker_Cfg.steps in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.zeta_full =
                             (uu___1.FStar_TypeChecker_Cfg.zeta_full);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                           FStar_TypeChecker_Cfg.unfold_until =
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.delta_constant);
                           FStar_TypeChecker_Cfg.unfold_only =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Cfg.unfold_fully =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Cfg.unfold_attr =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Cfg.unfold_qual =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Cfg.unfold_tac =
                             (uu___1.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___1.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1.FStar_TypeChecker_Cfg.for_extraction)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___.FStar_TypeChecker_Cfg.reifying)
                    } in
                  let stack' =
                    match stack1 with
                    | (UnivArgs (us, r))::stack'1 -> (UnivArgs (us, r)) ::
                        (Cfg (cfg, FStar_Pervasives_Native.None)) :: stack'1
                    | stack'1 -> (Cfg (cfg, FStar_Pervasives_Native.None)) ::
                        stack'1 in
                  FStar_Pervasives_Native.Some (cfg', stack')
              | Should_unfold_reify ->
                  let rec push e s =
                    match s with
                    | [] -> [e]
                    | (UnivArgs (us, r))::t ->
                        let uu___ = push e t in (UnivArgs (us, r)) :: uu___
                    | h::t -> e :: h :: t in
                  let ref =
                    let uu___ =
                      let uu___1 =
                        let uu___2 = FStar_Syntax_Syntax.lid_of_fv fv in
                        FStar_Const.Const_reflect uu___2 in
                      FStar_Syntax_Syntax.Tm_constant uu___1 in
                    FStar_Syntax_Syntax.mk uu___ FStar_Range.dummyRange in
                  let stack2 =
                    push
                      (App
                         (env1, ref, FStar_Pervasives_Native.None,
                           FStar_Range.dummyRange)) stack1 in
                  FStar_Pervasives_Native.Some (cfg, stack2)
let (on_domain_lids : FStar_Ident.lident Prims.list) =
  let fext_lid s =
    FStar_Ident.lid_of_path ["FStar"; "FunctionalExtensionality"; s]
      FStar_Range.dummyRange in
  FStar_All.pipe_right ["on_domain"; "on_dom"; "on_domain_g"; "on_dom_g"]
    (FStar_List.map fext_lid)
let (is_fext_on_domain :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t ->
    let is_on_dom fv =
      FStar_All.pipe_right on_domain_lids
        (FStar_List.existsb (fun l -> FStar_Syntax_Syntax.fv_eq_lid fv l)) in
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_app (hd, args) ->
        let uu___1 =
          let uu___2 = FStar_Syntax_Util.un_uinst hd in
          uu___2.FStar_Syntax_Syntax.n in
        (match uu___1 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStar_List.length args) = (Prims.of_int (3)))
             ->
             let f =
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStar_All.pipe_right args FStar_List.tl in
                   FStar_All.pipe_right uu___4 FStar_List.tl in
                 FStar_All.pipe_right uu___3 FStar_List.hd in
               FStar_All.pipe_right uu___2 FStar_Pervasives_Native.fst in
             FStar_Pervasives_Native.Some f
         | uu___2 -> FStar_Pervasives_Native.None)
    | uu___1 -> FStar_Pervasives_Native.None
let (is_partial_primop_app :
  FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun cfg ->
    fun t ->
      let uu___ = FStar_Syntax_Util.head_and_args t in
      match uu___ with
      | (hd, args) ->
          let uu___1 =
            let uu___2 = FStar_Syntax_Util.un_uinst hd in
            uu___2.FStar_Syntax_Syntax.n in
          (match uu___1 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu___2 = FStar_TypeChecker_Cfg.find_prim_step cfg fv in
               (match uu___2 with
                | FStar_Pervasives_Native.Some prim_step ->
                    prim_step.FStar_TypeChecker_Cfg.arity >
                      (FStar_List.length args)
                | FStar_Pervasives_Native.None -> false)
           | uu___2 -> false)
let rec (norm :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun t ->
          let t1 =
            if
              (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.norm_delayed
            then
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_delayed uu___1 ->
                   let uu___2 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print1 "NORM delayed: %s\n" uu___2
               | uu___1 -> ())
            else ();
            FStar_Syntax_Subst.compress t in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu___1 ->
               let uu___2 = FStar_Syntax_Print.tag_of_term t1 in
               let uu___3 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm in
               let uu___4 = FStar_Syntax_Print.term_to_string t1 in
               let uu___5 = FStar_Util.string_of_int (FStar_List.length env1) in
               let uu___6 =
                 let uu___7 =
                   let uu___8 = firstn (Prims.of_int (4)) stack1 in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu___8 in
                 stack_to_string uu___7 in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu___2 uu___3 uu___4 uu___5 uu___6);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu___2 ->
               let uu___3 = FStar_TypeChecker_Cfg.cfg_to_string cfg in
               FStar_Util.print1 ">>> cfg = %s\n" uu___3);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu___3 ->
                     let uu___4 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu___4);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_constant uu___2 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu___4 ->
                     let uu___5 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu___5);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_name uu___2 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu___4 ->
                     let uu___5 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu___5);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_lazy uu___2 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu___4 ->
                     let uu___5 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu___5);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu___2;
                 FStar_Syntax_Syntax.fv_delta = uu___3;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu___5 ->
                     let uu___6 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu___6);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu___2;
                 FStar_Syntax_Syntax.fv_delta = uu___3;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu___4);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu___6 ->
                     let uu___7 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n" uu___7);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid in
               let uu___2 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo in
               (match uu___2 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level uu___3) when
                    uu___3 = Prims.int_zero ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu___5 ->
                          let uu___6 = FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu___6);
                     rebuild cfg env1 stack1 t1)
                | uu___3 ->
                    let uu___4 =
                      decide_unfolding cfg env1 stack1
                        t1.FStar_Syntax_Syntax.pos fv qninfo in
                    (match uu___4 with
                     | FStar_Pervasives_Native.Some (cfg1, stack2) ->
                         do_unfold_fv cfg1 env1 stack2 t1 qninfo fv
                     | FStar_Pervasives_Native.None ->
                         rebuild cfg env1 stack1 t1))
           | FStar_Syntax_Syntax.Tm_quoted (qt, qi) ->
               let qi1 =
                 FStar_Syntax_Syntax.on_antiquoted (norm cfg env1 []) qi in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                   t1.FStar_Syntax_Syntax.pos in
               let uu___2 = closure_as_term cfg env1 t2 in
               rebuild cfg env1 stack1 uu___2
           | FStar_Syntax_Syntax.Tm_app (hd, args) when
               (should_consider_norm_requests cfg) &&
                 (let uu___2 = is_norm_request hd args in
                  uu___2 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu___3 = rejig_norm_request hd args in
                 norm cfg env1 stack1 uu___3))
           | FStar_Syntax_Syntax.Tm_app (hd, args) when
               (should_consider_norm_requests cfg) &&
                 (let uu___2 = is_norm_request hd args in
                  uu___2 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then
                  (let uu___3 = FStar_Syntax_Print.term_to_string hd in
                   let uu___4 = FStar_Syntax_Print.args_to_string args in
                   FStar_Util.print2
                     "Potential norm request with hd = %s and args = %s ... \n"
                     uu___3 uu___4)
                else ();
                (let cfg' =
                   let uu___3 = cfg in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___4 = cfg.FStar_TypeChecker_Cfg.steps in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___4.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___4.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___4.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.zeta_full =
                            (uu___4.FStar_TypeChecker_Cfg.zeta_full);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___4.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___4.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___4.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___4.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___4.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_qual =
                            (uu___4.FStar_TypeChecker_Cfg.unfold_qual);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___4.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___4.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___4.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___4.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___4.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___4.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___4.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___4.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___4.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___4.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___4.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___4.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___4.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___4.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___4.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___3.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___3.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___3.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___3.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___3.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___3.FStar_TypeChecker_Cfg.reifying)
                   } in
                 let uu___3 = get_norm_request cfg (norm cfg' env1 []) args in
                 match uu___3 with
                 | FStar_Pervasives_Native.None ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack2 =
                         FStar_All.pipe_right stack1
                           (FStar_List.fold_right
                              (fun uu___5 ->
                                 fun stack3 ->
                                   match uu___5 with
                                   | (a, aq) ->
                                       let uu___6 =
                                         let uu___7 =
                                           let uu___8 =
                                             let uu___9 =
                                               let uu___10 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None in
                                               (env1, a, uu___10, false) in
                                             Clos uu___9 in
                                           (uu___8, aq,
                                             (t1.FStar_Syntax_Syntax.pos)) in
                                         Arg uu___7 in
                                       uu___6 :: stack3) args) in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu___6 ->
                            let uu___7 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args) in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu___7);
                       norm cfg env1 stack2 hd))
                 | FStar_Pervasives_Native.Some (s, tm) when is_nbe_request s
                     ->
                     let tm' = closure_as_term cfg env1 tm in
                     let start = FStar_Util.now () in
                     let tm_norm = nbe_eval cfg s tm' in
                     let fin = FStar_Util.now () in
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let cfg'1 =
                           FStar_TypeChecker_Cfg.config' [] s
                             cfg.FStar_TypeChecker_Cfg.tcenv in
                         let uu___5 =
                           let uu___6 =
                             let uu___7 = FStar_Util.time_diff start fin in
                             FStar_Pervasives_Native.snd uu___7 in
                           FStar_Util.string_of_int uu___6 in
                         let uu___6 = FStar_Syntax_Print.term_to_string tm' in
                         let uu___7 =
                           FStar_TypeChecker_Cfg.cfg_to_string cfg'1 in
                         let uu___8 =
                           FStar_Syntax_Print.term_to_string tm_norm in
                         FStar_Util.print4
                           "NBE result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                           uu___5 uu___6 uu___7 uu___8)
                      else ();
                      rebuild cfg env1 stack1 tm_norm)
                 | FStar_Pervasives_Native.Some (s, tm) ->
                     let delta_level =
                       let uu___4 =
                         FStar_All.pipe_right s
                           (FStar_Util.for_some
                              (fun uu___5 ->
                                 match uu___5 with
                                 | FStar_TypeChecker_Env.UnfoldUntil uu___6
                                     -> true
                                 | FStar_TypeChecker_Env.UnfoldOnly uu___6 ->
                                     true
                                 | FStar_TypeChecker_Env.UnfoldFully uu___6
                                     -> true
                                 | uu___6 -> false)) in
                       if uu___4
                       then
                         [FStar_TypeChecker_Env.Unfold
                            FStar_Syntax_Syntax.delta_constant]
                       else
                         if
                           (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                         then
                           [FStar_TypeChecker_Env.Eager_unfolding_only;
                           FStar_TypeChecker_Env.InliningDelta]
                         else [FStar_TypeChecker_Env.NoDelta] in
                     let cfg'1 =
                       let uu___4 = cfg in
                       let uu___5 =
                         let uu___6 = FStar_TypeChecker_Cfg.to_fsteps s in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___6.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___6.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___6.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.zeta_full =
                             (uu___6.FStar_TypeChecker_Cfg.zeta_full);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___6.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___6.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___6.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___6.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                           FStar_TypeChecker_Cfg.unfold_until =
                             (uu___6.FStar_TypeChecker_Cfg.unfold_until);
                           FStar_TypeChecker_Cfg.unfold_only =
                             (uu___6.FStar_TypeChecker_Cfg.unfold_only);
                           FStar_TypeChecker_Cfg.unfold_fully =
                             (uu___6.FStar_TypeChecker_Cfg.unfold_fully);
                           FStar_TypeChecker_Cfg.unfold_attr =
                             (uu___6.FStar_TypeChecker_Cfg.unfold_attr);
                           FStar_TypeChecker_Cfg.unfold_qual =
                             (uu___6.FStar_TypeChecker_Cfg.unfold_qual);
                           FStar_TypeChecker_Cfg.unfold_tac =
                             (uu___6.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___6.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___6.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___6.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___6.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___6.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___6.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___6.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___6.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___6.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___6.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request = true;
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___6.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___6.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction)
                         } in
                       {
                         FStar_TypeChecker_Cfg.steps = uu___5;
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___4.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___4.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level = delta_level;
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___4.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___4.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___4.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                         FStar_TypeChecker_Cfg.reifying =
                           (uu___4.FStar_TypeChecker_Cfg.reifying)
                       } in
                     let stack' =
                       let debug =
                         if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           let uu___4 =
                             let uu___5 = FStar_Util.now () in (tm, uu___5) in
                           FStar_Pervasives_Native.Some uu___4
                         else FStar_Pervasives_Native.None in
                       (Cfg (cfg, debug)) :: stack1 in
                     norm cfg'1 env1 stack' tm))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env1 u in
               let uu___2 =
                 FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env1 stack1 uu___2
           | FStar_Syntax_Syntax.Tm_uinst (t', us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env1 stack1 t'
               else
                 (let us1 =
                    let uu___3 =
                      let uu___4 = FStar_List.map (norm_universe cfg env1) us in
                      (uu___4, (t1.FStar_Syntax_Syntax.pos)) in
                    UnivArgs uu___3 in
                  let stack2 = us1 :: stack1 in norm cfg env1 stack2 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu___2 = lookup_bvar env1 x in
               (match uu___2 with
                | Univ uu___3 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy -> failwith "Term variable not found"
                | Clos (env2, t0, r, fix) ->
                    if
                      ((Prims.op_Negation fix) ||
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                        ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full
                    then
                      let uu___3 = FStar_ST.op_Bang r in
                      (match uu___3 with
                       | FStar_Pervasives_Native.Some (env3, t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu___5 ->
                                 let uu___6 =
                                   FStar_Syntax_Print.term_to_string t1 in
                                 let uu___7 =
                                   FStar_Syntax_Print.term_to_string t' in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu___6
                                   uu___7);
                            (let uu___5 = maybe_weakly_reduced t' in
                             if uu___5
                             then
                               match stack1 with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env3 stack1 t'
                               | uu___6 -> norm cfg env3 stack1 t'
                             else rebuild cfg env3 stack1 t'))
                       | FStar_Pervasives_Native.None ->
                           norm cfg env2 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env2 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) ->
               (match stack1 with
                | (UnivArgs uu___2)::uu___3 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c, uu___2, uu___3))::stack_rest ->
                    (match c with
                     | Univ uu___4 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env1)
                           stack_rest t1
                     | uu___4 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu___6 ->
                                    let uu___7 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n" uu___7);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env1) stack_rest body)
                          | b::tl ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu___6 ->
                                    let uu___7 = closure_to_string c in
                                    FStar_Util.print1 "\tShifted %s\n" uu___7);
                               (let body1 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos in
                                norm cfg
                                  (((FStar_Pervasives_Native.Some b), c) ::
                                  env1) stack_rest body1))))
                | (MemoLazy r)::stack2 ->
                    (set_memo cfg r (env1, t1);
                     FStar_TypeChecker_Cfg.log cfg
                       (fun uu___4 ->
                          let uu___5 = FStar_Syntax_Print.term_to_string t1 in
                          FStar_Util.print1 "\tSet memo %s\n" uu___5);
                     norm cfg env1 stack2 t1)
                | (Cfg uu___2)::uu___3 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu___5 = FStar_Syntax_Subst.open_term' bs body in
                       match uu___5 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 -> fun uu___6 -> dummy :: env2)
                                  env1) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu___6 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu___6)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___6 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___6.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___6.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu___6 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu___7 ->
                                 let uu___8 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu___8);
                            (let stack2 =
                               (Cfg (cfg, FStar_Pervasives_Native.None)) ::
                               stack1 in
                             let cfg1 =
                               let uu___7 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___7.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___7.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___7.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___7.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___7.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___7.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___7.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___7.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Match uu___2)::uu___3 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu___5 = FStar_Syntax_Subst.open_term' bs body in
                       match uu___5 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 -> fun uu___6 -> dummy :: env2)
                                  env1) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu___6 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu___6)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___6 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___6.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___6.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu___6 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu___7 ->
                                 let uu___8 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu___8);
                            (let stack2 =
                               (Cfg (cfg, FStar_Pervasives_Native.None)) ::
                               stack1 in
                             let cfg1 =
                               let uu___7 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___7.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___7.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___7.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___7.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___7.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___7.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___7.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___7.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu___2)::uu___3 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu___5 = FStar_Syntax_Subst.open_term' bs body in
                       match uu___5 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 -> fun uu___6 -> dummy :: env2)
                                  env1) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu___6 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu___6)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___6 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___6.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___6.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu___6 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu___7 ->
                                 let uu___8 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu___8);
                            (let stack2 =
                               (Cfg (cfg, FStar_Pervasives_Native.None)) ::
                               stack1 in
                             let cfg1 =
                               let uu___7 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___7.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___7.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___7.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___7.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___7.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___7.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___7.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___7.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu___2)::uu___3 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu___5 = FStar_Syntax_Subst.open_term' bs body in
                       match uu___5 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 -> fun uu___6 -> dummy :: env2)
                                  env1) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu___6 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu___6)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___6 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___6.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___6.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu___6 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu___7 ->
                                 let uu___8 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu___8);
                            (let stack2 =
                               (Cfg (cfg, FStar_Pervasives_Native.None)) ::
                               stack1 in
                             let cfg1 =
                               let uu___7 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___7.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___7.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___7.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___7.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___7.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___7.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___7.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___7.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu___2)::uu___3 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu___5 = FStar_Syntax_Subst.open_term' bs body in
                       match uu___5 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 -> fun uu___6 -> dummy :: env2)
                                  env1) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu___6 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu___6)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___6 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___6.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___6.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu___6 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu___7 ->
                                 let uu___8 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu___8);
                            (let stack2 =
                               (Cfg (cfg, FStar_Pervasives_Native.None)) ::
                               stack1 in
                             let cfg1 =
                               let uu___7 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___7.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___7.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___7.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___7.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___7.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___7.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___7.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___7.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (CBVApp uu___2)::uu___3 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu___5 = FStar_Syntax_Subst.open_term' bs body in
                       match uu___5 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 -> fun uu___6 -> dummy :: env2)
                                  env1) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu___6 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu___6)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___6 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___6.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___6.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu___6 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu___7 ->
                                 let uu___8 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu___8);
                            (let stack2 =
                               (Cfg (cfg, FStar_Pervasives_Native.None)) ::
                               stack1 in
                             let cfg1 =
                               let uu___7 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___7.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___7.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___7.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___7.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___7.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___7.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___7.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___7.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu___2)::uu___3 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu___5 = FStar_Syntax_Subst.open_term' bs body in
                       match uu___5 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 -> fun uu___6 -> dummy :: env2)
                                  env1) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu___6 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu___6)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___6 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___6.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___6.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu___6 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu___7 ->
                                 let uu___8 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu___8);
                            (let stack2 =
                               (Cfg (cfg, FStar_Pervasives_Native.None)) ::
                               stack1 in
                             let cfg1 =
                               let uu___7 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___7.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___7.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___7.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___7.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___7.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___7.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___7.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___7.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu___3 = FStar_Syntax_Subst.open_term' bs body in
                       match uu___3 with
                       | (bs1, body1, opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2 -> fun uu___4 -> dummy :: env2)
                                  env1) in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2 ->
                                          let uu___4 =
                                            FStar_Syntax_Subst.subst opening
                                              t2 in
                                          norm cfg env' [] uu___4)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening) in
                                 FStar_Pervasives_Native.Some
                                   (let uu___4 = rc in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___4.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___4.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu___4 -> lopt in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu___5 ->
                                 let uu___6 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1) in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu___6);
                            (let stack2 =
                               (Cfg (cfg, FStar_Pervasives_Native.None)) ::
                               stack1 in
                             let cfg1 =
                               let uu___5 = cfg in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___5.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___5.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___5.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___5.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___5.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___5.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___5.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___5.FStar_TypeChecker_Cfg.reifying)
                               } in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1))))
           | FStar_Syntax_Syntax.Tm_app (head, args) ->
               let strict_args =
                 let uu___2 =
                   let uu___3 =
                     let uu___4 =
                       FStar_All.pipe_right head FStar_Syntax_Util.unascribe in
                     FStar_All.pipe_right uu___4 FStar_Syntax_Util.un_uinst in
                   uu___3.FStar_Syntax_Syntax.n in
                 match uu___2 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     FStar_TypeChecker_Env.fv_has_strict_args
                       cfg.FStar_TypeChecker_Cfg.tcenv fv
                 | uu___3 -> FStar_Pervasives_Native.None in
               (match strict_args with
                | FStar_Pervasives_Native.None ->
                    let stack2 =
                      FStar_All.pipe_right stack1
                        (FStar_List.fold_right
                           (fun uu___2 ->
                              fun stack3 ->
                                match uu___2 with
                                | (a, aq) ->
                                    let uu___3 =
                                      let uu___4 =
                                        let uu___5 =
                                          let uu___6 =
                                            let uu___7 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None in
                                            (env1, a, uu___7, false) in
                                          Clos uu___6 in
                                        (uu___5, aq,
                                          (t1.FStar_Syntax_Syntax.pos)) in
                                      Arg uu___4 in
                                    uu___3 :: stack3) args) in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu___3 ->
                          let uu___4 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args) in
                          FStar_Util.print1 "\tPushed %s arguments\n" uu___4);
                     norm cfg env1 stack2 head)
                | FStar_Pervasives_Native.Some strict_args1 ->
                    let norm_args =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu___2 ->
                              match uu___2 with
                              | (a, i) ->
                                  let uu___3 = norm cfg env1 [] a in
                                  (uu___3, i))) in
                    let norm_args_len = FStar_List.length norm_args in
                    let uu___2 =
                      FStar_All.pipe_right strict_args1
                        (FStar_List.for_all
                           (fun i ->
                              if i >= norm_args_len
                              then false
                              else
                                (let uu___4 = FStar_List.nth norm_args i in
                                 match uu___4 with
                                 | (arg_i, uu___5) ->
                                     let uu___6 =
                                       let uu___7 =
                                         FStar_All.pipe_right arg_i
                                           FStar_Syntax_Util.unascribe in
                                       FStar_All.pipe_right uu___7
                                         FStar_Syntax_Util.head_and_args in
                                     (match uu___6 with
                                      | (head1, uu___7) ->
                                          let uu___8 =
                                            let uu___9 =
                                              FStar_Syntax_Util.un_uinst
                                                head1 in
                                            uu___9.FStar_Syntax_Syntax.n in
                                          (match uu___8 with
                                           | FStar_Syntax_Syntax.Tm_constant
                                               uu___9 -> true
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               let uu___9 =
                                                 FStar_Syntax_Syntax.lid_of_fv
                                                   fv in
                                               FStar_TypeChecker_Env.is_datacon
                                                 cfg.FStar_TypeChecker_Cfg.tcenv
                                                 uu___9
                                           | uu___9 -> false))))) in
                    if uu___2
                    then
                      let stack2 =
                        FStar_All.pipe_right stack1
                          (FStar_List.fold_right
                             (fun uu___3 ->
                                fun stack3 ->
                                  match uu___3 with
                                  | (a, aq) ->
                                      let uu___4 =
                                        let uu___5 =
                                          let uu___6 =
                                            let uu___7 =
                                              let uu___8 =
                                                FStar_Util.mk_ref
                                                  (FStar_Pervasives_Native.Some
                                                     ([], a)) in
                                              (env1, a, uu___8, false) in
                                            Clos uu___7 in
                                          (uu___6, aq,
                                            (t1.FStar_Syntax_Syntax.pos)) in
                                        Arg uu___5 in
                                      uu___4 :: stack3) norm_args) in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu___4 ->
                            let uu___5 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args) in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu___5);
                       norm cfg env1 stack2 head)
                    else
                      (let head1 = closure_as_term cfg env1 head in
                       let term =
                         FStar_Syntax_Syntax.mk_Tm_app head1 norm_args
                           t1.FStar_Syntax_Syntax.pos in
                       rebuild cfg env1 stack1 term))
           | FStar_Syntax_Syntax.Tm_refine (x, uu___2) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
               -> norm cfg env1 stack1 x.FStar_Syntax_Syntax.sort
           | FStar_Syntax_Syntax.Tm_refine (x, f) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 (match (env1, stack1) with
                  | ([], []) ->
                      let t_x = norm cfg env1 [] x.FStar_Syntax_Syntax.sort in
                      let t2 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_refine
                             ((let uu___2 = x in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env1 stack1 t2
                  | uu___2 ->
                      let uu___3 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack1 uu___3)
               else
                 (let t_x = norm cfg env1 [] x.FStar_Syntax_Syntax.sort in
                  let uu___3 =
                    let uu___4 =
                      let uu___5 = FStar_Syntax_Syntax.mk_binder x in
                      [uu___5] in
                    FStar_Syntax_Subst.open_term uu___4 f in
                  match uu___3 with
                  | (closing, f1) ->
                      let f2 = norm cfg (dummy :: env1) [] f1 in
                      let t2 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 = FStar_Syntax_Subst.close closing f2 in
                            ((let uu___7 = x in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___7.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___7.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu___6) in
                          FStar_Syntax_Syntax.Tm_refine uu___5 in
                        FStar_Syntax_Syntax.mk uu___4
                          t1.FStar_Syntax_Syntax.pos in
                      rebuild cfg env1 stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu___2 = closure_as_term cfg env1 t1 in
                 rebuild cfg env1 stack1 uu___2
               else
                 (let uu___3 = FStar_Syntax_Subst.open_comp bs c in
                  match uu___3 with
                  | (bs1, c1) ->
                      let c2 =
                        let uu___4 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env2 -> fun uu___5 -> dummy :: env2) env1) in
                        norm_comp cfg uu___4 c1 in
                      let t2 =
                        let uu___4 = norm_binders cfg env1 bs1 in
                        FStar_Syntax_Util.arrow uu___4 c2 in
                      rebuild cfg env1 stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env1 stack1 t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11, (tc, tacopt), l) ->
               (match stack1 with
                | (Match uu___2)::uu___3 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu___5 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (Arg uu___2)::uu___3 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu___5 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (App
                    (uu___2,
                     {
                       FStar_Syntax_Syntax.n =
                         FStar_Syntax_Syntax.Tm_constant
                         (FStar_Const.Const_reify);
                       FStar_Syntax_Syntax.pos = uu___3;
                       FStar_Syntax_Syntax.vars = uu___4;_},
                     uu___5, uu___6))::uu___7
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu___9 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (MemoLazy uu___2)::uu___3 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu___5 ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | uu___2 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu___4 ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env1 [] t11 in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu___5 ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Pervasives.Inl t2 ->
                             let uu___5 = norm cfg env1 [] t2 in
                             FStar_Pervasives.Inl uu___5
                         | FStar_Pervasives.Inr c ->
                             let uu___5 = norm_comp cfg env1 c in
                             FStar_Pervasives.Inr uu___5 in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env1 []) in
                       match stack1 with
                       | (Cfg (cfg1, dbg))::stack2 ->
                           (maybe_debug cfg1 t12 dbg;
                            (let t2 =
                               let uu___6 =
                                 let uu___7 =
                                   let uu___8 =
                                     FStar_Syntax_Util.unascribe t12 in
                                   (uu___8, (tc1, tacopt1), l) in
                                 FStar_Syntax_Syntax.Tm_ascribed uu___7 in
                               FStar_Syntax_Syntax.mk uu___6
                                 t1.FStar_Syntax_Syntax.pos in
                             norm cfg1 env1 stack2 t2))
                       | uu___5 ->
                           let uu___6 =
                             let uu___7 =
                               let uu___8 =
                                 let uu___9 = FStar_Syntax_Util.unascribe t12 in
                                 (uu___9, (tc1, tacopt1), l) in
                               FStar_Syntax_Syntax.Tm_ascribed uu___8 in
                             FStar_Syntax_Syntax.mk uu___7
                               t1.FStar_Syntax_Syntax.pos in
                           rebuild cfg env1 stack1 uu___6))))
           | FStar_Syntax_Syntax.Tm_match (head, asc_opt, branches1) ->
               let stack2 =
                 (Match
                    (env1, asc_opt, branches1, cfg,
                      (t1.FStar_Syntax_Syntax.pos)))
                 :: stack1 in
               if
                 ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                    &&
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weakly_reduce_scrutinee)
                   &&
                   (Prims.op_Negation
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak)
               then
                 let cfg' =
                   let uu___2 = cfg in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___3 = cfg.FStar_TypeChecker_Cfg.steps in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___3.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___3.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___3.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.zeta_full =
                            (uu___3.FStar_TypeChecker_Cfg.zeta_full);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___3.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___3.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___3.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___3.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___3.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___3.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___3.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_qual =
                            (uu___3.FStar_TypeChecker_Cfg.unfold_qual);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___3.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___3.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___3.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___3.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___3.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___3.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___3.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___3.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___3.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___3.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___3.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___3.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___3.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___3.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___3.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___2.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___2.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___2.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___2.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___2.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___2.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___2.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___2.FStar_TypeChecker_Cfg.reifying)
                   } in
                 norm cfg' env1 ((Cfg (cfg, FStar_Pervasives_Native.None)) ::
                   stack2) head
               else norm cfg env1 stack2 head
           | FStar_Syntax_Syntax.Tm_let ((b, lbs), lbody) when
               (FStar_Syntax_Syntax.is_top_level lbs) &&
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               ->
               let lbs1 =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb ->
                         let uu___2 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs in
                         match uu___2 with
                         | (openings, lbunivs) ->
                             let cfg1 =
                               let uu___3 = cfg in
                               let uu___4 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___3.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu___4;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___3.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___3.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___3.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___3.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___3.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___3.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___3.FStar_TypeChecker_Cfg.reifying)
                               } in
                             let norm1 t2 =
                               let uu___3 =
                                 let uu___4 =
                                   FStar_Syntax_Subst.subst openings t2 in
                                 norm cfg1 env1 [] uu___4 in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu___3 in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef in
                             let uu___3 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___3.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___3.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___3.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___3.FStar_Syntax_Syntax.lbpos)
                             })) in
               let uu___2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos in
               rebuild cfg env1 stack1 uu___2
           | FStar_Syntax_Syntax.Tm_let
               ((uu___2,
                 { FStar_Syntax_Syntax.lbname = FStar_Pervasives.Inr uu___3;
                   FStar_Syntax_Syntax.lbunivs = uu___4;
                   FStar_Syntax_Syntax.lbtyp = uu___5;
                   FStar_Syntax_Syntax.lbeff = uu___6;
                   FStar_Syntax_Syntax.lbdef = uu___7;
                   FStar_Syntax_Syntax.lbattrs = uu___8;
                   FStar_Syntax_Syntax.lbpos = uu___9;_}::uu___10),
                uu___11)
               -> rebuild cfg env1 stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
               let uu___2 =
                 FStar_TypeChecker_Cfg.should_reduce_local_let cfg lb in
               if uu___2
               then
                 let binder =
                   let uu___3 = FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                   FStar_Syntax_Syntax.mk_binder uu___3 in
                 let def =
                   FStar_Syntax_Util.unmeta_lift lb.FStar_Syntax_Syntax.lbdef in
                 let env2 =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         let uu___6 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None in
                         (env1, def, uu___6, false) in
                       Clos uu___5 in
                     ((FStar_Pervasives_Native.Some binder), uu___4) in
                   uu___3 :: env1 in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu___4 ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env2 stack1 body)
               else
                 (let uu___4 =
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
                      &&
                      (let uu___5 =
                         FStar_TypeChecker_Env.norm_eff_name
                           cfg.FStar_TypeChecker_Cfg.tcenv
                           lb.FStar_Syntax_Syntax.lbeff in
                       FStar_Syntax_Util.is_div_effect uu___5) in
                  if uu___4
                  then
                    let ffun =
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              let uu___9 =
                                FStar_All.pipe_right
                                  lb.FStar_Syntax_Syntax.lbname
                                  FStar_Util.left in
                              FStar_Syntax_Syntax.mk_binder uu___9 in
                            [uu___8] in
                          (uu___7, body, FStar_Pervasives_Native.None) in
                        FStar_Syntax_Syntax.Tm_abs uu___6 in
                      FStar_Syntax_Syntax.mk uu___5
                        t1.FStar_Syntax_Syntax.pos in
                    let stack2 =
                      (CBVApp
                         (env1, ffun, FStar_Pervasives_Native.None,
                           (t1.FStar_Syntax_Syntax.pos)))
                      :: stack1 in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu___6 ->
                          FStar_Util.print_string
                            "+++ Evaluating DIV Tm_let\n");
                     norm cfg env1 stack2 lb.FStar_Syntax_Syntax.lbdef)
                  else
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu___7 ->
                            FStar_Util.print_string
                              "+++ Not touching Tm_let\n");
                       (let uu___7 = closure_as_term cfg env1 t1 in
                        rebuild cfg env1 stack1 uu___7))
                    else
                      (let uu___7 =
                         let uu___8 =
                           let uu___9 =
                             let uu___10 =
                               FStar_All.pipe_right
                                 lb.FStar_Syntax_Syntax.lbname
                                 FStar_Util.left in
                             FStar_All.pipe_right uu___10
                               FStar_Syntax_Syntax.mk_binder in
                           [uu___9] in
                         FStar_Syntax_Subst.open_term uu___8 body in
                       match uu___7 with
                       | (bs, body1) ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu___9 ->
                                 FStar_Util.print_string
                                   "+++ Normalizing Tm_let -- type");
                            (let ty =
                               norm cfg env1 [] lb.FStar_Syntax_Syntax.lbtyp in
                             let lbname =
                               let x =
                                 let uu___9 = FStar_List.hd bs in
                                 uu___9.FStar_Syntax_Syntax.binder_bv in
                               FStar_Pervasives.Inl
                                 (let uu___9 = x in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___9.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___9.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = ty
                                  }) in
                             FStar_TypeChecker_Cfg.log cfg
                               (fun uu___10 ->
                                  FStar_Util.print_string
                                    "+++ Normalizing Tm_let -- definiens\n");
                             (let lb1 =
                                let uu___10 = lb in
                                let uu___11 =
                                  norm cfg env1 []
                                    lb.FStar_Syntax_Syntax.lbdef in
                                let uu___12 =
                                  FStar_List.map (norm cfg env1 [])
                                    lb.FStar_Syntax_Syntax.lbattrs in
                                {
                                  FStar_Syntax_Syntax.lbname = lbname;
                                  FStar_Syntax_Syntax.lbunivs =
                                    (uu___10.FStar_Syntax_Syntax.lbunivs);
                                  FStar_Syntax_Syntax.lbtyp = ty;
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___10.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = uu___11;
                                  FStar_Syntax_Syntax.lbattrs = uu___12;
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___10.FStar_Syntax_Syntax.lbpos)
                                } in
                              let env' =
                                FStar_All.pipe_right bs
                                  (FStar_List.fold_left
                                     (fun env2 ->
                                        fun uu___10 -> dummy :: env2) env1) in
                              let stack2 =
                                (Cfg (cfg, FStar_Pervasives_Native.None)) ::
                                stack1 in
                              let cfg1 =
                                let uu___10 = cfg in
                                {
                                  FStar_TypeChecker_Cfg.steps =
                                    (uu___10.FStar_TypeChecker_Cfg.steps);
                                  FStar_TypeChecker_Cfg.tcenv =
                                    (uu___10.FStar_TypeChecker_Cfg.tcenv);
                                  FStar_TypeChecker_Cfg.debug =
                                    (uu___10.FStar_TypeChecker_Cfg.debug);
                                  FStar_TypeChecker_Cfg.delta_level =
                                    (uu___10.FStar_TypeChecker_Cfg.delta_level);
                                  FStar_TypeChecker_Cfg.primitive_steps =
                                    (uu___10.FStar_TypeChecker_Cfg.primitive_steps);
                                  FStar_TypeChecker_Cfg.strong = true;
                                  FStar_TypeChecker_Cfg.memoize_lazy =
                                    (uu___10.FStar_TypeChecker_Cfg.memoize_lazy);
                                  FStar_TypeChecker_Cfg.normalize_pure_lets =
                                    (uu___10.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                  FStar_TypeChecker_Cfg.reifying =
                                    (uu___10.FStar_TypeChecker_Cfg.reifying)
                                } in
                              FStar_TypeChecker_Cfg.log cfg1
                                (fun uu___11 ->
                                   FStar_Util.print_string
                                     "+++ Normalizing Tm_let -- body\n");
                              norm cfg1 env'
                                ((Let
                                    (env1, bs, lb1,
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack2) body1)))))
           | FStar_Syntax_Syntax.Tm_let ((true, lbs), body) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                 ||
                 (((Prims.op_Negation
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                     &&
                     (Prims.op_Negation
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full))
                    &&
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.pure_subterms_within_computations)
               ->
               let uu___2 = FStar_Syntax_Subst.open_let_rec lbs body in
               (match uu___2 with
                | (lbs1, body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb ->
                           let ty =
                             norm cfg env1 [] lb.FStar_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu___3 =
                               let uu___4 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___4.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___4.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               } in
                             FStar_Pervasives.Inl uu___3 in
                           let uu___3 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef in
                           match uu___3 with
                           | (xs, def_body, lopt) ->
                               let xs1 = norm_binders cfg env1 xs in
                               let env2 =
                                 let uu___4 =
                                   FStar_List.map (fun uu___5 -> dummy) xs1 in
                                 let uu___5 =
                                   let uu___6 =
                                     FStar_List.map (fun uu___7 -> dummy)
                                       lbs1 in
                                   FStar_List.append uu___6 env1 in
                                 FStar_List.append uu___4 uu___5 in
                               let def_body1 = norm cfg env2 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu___4 =
                                       let uu___5 = rc in
                                       let uu___6 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env2 []) in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___5.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu___6;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___5.FStar_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu___4
                                 | uu___4 -> lopt in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1 in
                               let uu___4 = lb in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___4.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___4.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___4.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___4.FStar_Syntax_Syntax.lbpos)
                               }) lbs1 in
                    let env' =
                      let uu___3 = FStar_List.map (fun uu___4 -> dummy) lbs2 in
                      FStar_List.append uu___3 env1 in
                    let body2 = norm cfg env' [] body1 in
                    let uu___3 = FStar_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu___3 with
                     | (lbs3, body3) ->
                         let t2 =
                           let uu___4 = t1 in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___4.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___4.FStar_Syntax_Syntax.vars)
                           } in
                         rebuild cfg env1 stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs, body) when
               (Prims.op_Negation
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                 &&
                 (Prims.op_Negation
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full)
               ->
               let uu___2 = closure_as_term cfg env1 t1 in
               rebuild cfg env1 stack1 uu___2
           | FStar_Syntax_Syntax.Tm_let (lbs, body) ->
               let uu___2 =
                 FStar_List.fold_right
                   (fun lb ->
                      fun uu___3 ->
                        match uu___3 with
                        | (rec_env, memos, i) ->
                            let bv =
                              let uu___4 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___4.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___4.FStar_Syntax_Syntax.sort)
                              } in
                            let f_i = FStar_Syntax_Syntax.bv_to_tm bv in
                            let fix_f_i =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos in
                            let memo =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None in
                            let rec_env1 =
                              (FStar_Pervasives_Native.None,
                                (Clos (env1, fix_f_i, memo, true)))
                              :: rec_env in
                            (rec_env1, (memo :: memos), (i + Prims.int_one)))
                   (FStar_Pervasives_Native.snd lbs)
                   (env1, [], Prims.int_zero) in
               (match uu___2 with
                | (rec_env, memos, uu___3) ->
                    let uu___4 =
                      FStar_List.map2
                        (fun lb ->
                           fun memo ->
                             FStar_ST.op_Colon_Equals memo
                               (FStar_Pervasives_Native.Some
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef))))
                        (FStar_Pervasives_Native.snd lbs) memos in
                    let body_env =
                      FStar_List.fold_right
                        (fun lb ->
                           fun env2 ->
                             let uu___5 =
                               let uu___6 =
                                 let uu___7 =
                                   let uu___8 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu___8, false) in
                                 Clos uu___7 in
                               (FStar_Pervasives_Native.None, uu___6) in
                             uu___5 :: env2)
                        (FStar_Pervasives_Native.snd lbs) env1 in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head, m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu___3 ->
                     let uu___4 = FStar_Syntax_Print.metadata_to_string m in
                     FStar_Util.print1 ">> metadata = %s\n" uu___4);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1, t2) ->
                     reduce_impure_comp cfg env1 stack1 head
                       (FStar_Pervasives.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t2) ->
                     reduce_impure_comp cfg env1 stack1 head
                       (FStar_Pervasives.Inr (m1, m')) t2
                 | uu___3 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env1 stack1 head
                     else
                       (match stack1 with
                        | uu___5::uu___6 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l, r, uu___7) ->
                                 norm cfg env1 ((Meta (env1, m, r)) ::
                                   stack1) head
                             | FStar_Syntax_Syntax.Meta_pattern (names, args)
                                 ->
                                 let args1 = norm_pattern_args cfg env1 args in
                                 let names1 =
                                   FStar_All.pipe_right names
                                     (FStar_List.map (norm cfg env1 [])) in
                                 norm cfg env1
                                   ((Meta
                                       (env1,
                                         (FStar_Syntax_Syntax.Meta_pattern
                                            (names1, args1)),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack1) head
                             | uu___7 -> norm cfg env1 stack1 head)
                        | [] ->
                            let head1 = norm cfg env1 [] head in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern
                                  (names, args) ->
                                  let names1 =
                                    FStar_All.pipe_right names
                                      (FStar_List.map (norm cfg env1 [])) in
                                  let uu___5 =
                                    let uu___6 =
                                      norm_pattern_args cfg env1 args in
                                    (names1, uu___6) in
                                  FStar_Syntax_Syntax.Meta_pattern uu___5
                              | uu___5 -> m in
                            let t2 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (head1, m1))
                                t1.FStar_Syntax_Syntax.pos in
                            rebuild cfg env1 stack1 t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu___2 ->
               failwith "impossible: Tm_delayed on norm"
           | FStar_Syntax_Syntax.Tm_uvar uu___2 ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
               then
                 let uu___3 =
                   let uu___4 =
                     FStar_Range.string_of_range t1.FStar_Syntax_Syntax.pos in
                   let uu___5 = FStar_Syntax_Print.term_to_string t1 in
                   FStar_Util.format2
                     "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                     uu___4 uu___5 in
                 failwith uu___3
               else
                 (let uu___4 = inline_closure_env cfg env1 [] t1 in
                  rebuild cfg env1 stack1 uu___4))
and (do_unfold_fv :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_TypeChecker_Env.qninfo ->
            FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun t0 ->
          fun qninfo ->
            fun f ->
              let uu___ =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo in
              match uu___ with
              | FStar_Pervasives_Native.None ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu___2 ->
                        let uu___3 = FStar_Syntax_Print.fv_to_string f in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu___3);
                   rebuild cfg env1 stack1 t0)
              | FStar_Pervasives_Native.Some (us, t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu___2 ->
                        let uu___3 = FStar_Syntax_Print.term_to_string t0 in
                        let uu___4 = FStar_Syntax_Print.term_to_string t in
                        FStar_Util.print2 " >> Unfolded %s to %s\n" uu___3
                          uu___4);
                   (let t1 =
                      if
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_until
                          =
                          (FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.delta_constant)
                      then t
                      else
                        FStar_Syntax_Subst.set_use_range
                          t0.FStar_Syntax_Syntax.pos t in
                    let n = FStar_List.length us in
                    if n > Prims.int_zero
                    then
                      match stack1 with
                      | (UnivArgs (us', uu___2))::stack2 ->
                          ((let uu___4 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm") in
                            if uu___4
                            then
                              FStar_List.iter
                                (fun x ->
                                   let uu___5 =
                                     FStar_Syntax_Print.univ_to_string x in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu___5) us'
                            else ());
                           (let env2 =
                              FStar_All.pipe_right us'
                                (FStar_List.fold_left
                                   (fun env3 ->
                                      fun u ->
                                        (FStar_Pervasives_Native.None,
                                          (Univ u))
                                        :: env3) env1) in
                            norm cfg env2 stack2 t1))
                      | uu___2 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env1 stack1 t1
                      | uu___2 ->
                          let uu___3 =
                            let uu___4 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu___4 in
                          failwith uu___3
                    else norm cfg env1 stack1 t1))
and (reduce_impure_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      stack ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.monad_name,
            (FStar_Syntax_Syntax.monad_name * FStar_Syntax_Syntax.monad_name))
            FStar_Pervasives.either ->
            FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun head ->
          fun m ->
            fun t ->
              let t1 = norm cfg env1 [] t in
              let uu___ =
                if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.pure_subterms_within_computations
                then
                  let new_steps =
                    [FStar_TypeChecker_Env.PureSubtermsWithinComputations;
                    FStar_TypeChecker_Env.Primops;
                    FStar_TypeChecker_Env.AllowUnboundUniverses;
                    FStar_TypeChecker_Env.EraseUniverses;
                    FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                    FStar_TypeChecker_Env.Inlining] in
                  let cfg' =
                    let uu___1 = cfg in
                    let uu___2 =
                      FStar_List.fold_right
                        FStar_TypeChecker_Cfg.fstep_add_one new_steps
                        cfg.FStar_TypeChecker_Cfg.steps in
                    {
                      FStar_TypeChecker_Cfg.steps = uu___2;
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        [FStar_TypeChecker_Env.InliningDelta;
                        FStar_TypeChecker_Env.Eager_unfolding_only];
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1.FStar_TypeChecker_Cfg.reifying)
                    } in
                  (cfg', ((Cfg (cfg, FStar_Pervasives_Native.None)) ::
                    stack1))
                else (cfg, stack1) in
              match uu___ with
              | (cfg1, stack2) ->
                  let metadata =
                    match m with
                    | FStar_Pervasives.Inl m1 ->
                        FStar_Syntax_Syntax.Meta_monadic (m1, t1)
                    | FStar_Pervasives.Inr (m1, m') ->
                        FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t1) in
                  norm cfg1 env1
                    ((Meta (env1, metadata, (head.FStar_Syntax_Syntax.pos)))
                    :: stack2) head
and (do_reify_monadic :
  (unit -> FStar_Syntax_Syntax.term) ->
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.monad_name ->
              FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun fallback ->
    fun cfg ->
      fun env1 ->
        fun stack1 ->
          fun top ->
            fun m ->
              fun t ->
                (match stack1 with
                 | (App
                     (uu___1,
                      {
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify);
                        FStar_Syntax_Syntax.pos = uu___2;
                        FStar_Syntax_Syntax.vars = uu___3;_},
                      uu___4, uu___5))::uu___6
                     -> ()
                 | uu___1 ->
                     let uu___2 =
                       let uu___3 = stack_to_string stack1 in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu___3 in
                     failwith uu___2);
                (let top0 = top in
                 let top1 = FStar_Syntax_Util.unascribe top in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu___2 ->
                      let uu___3 = FStar_Syntax_Print.tag_of_term top1 in
                      let uu___4 = FStar_Syntax_Print.term_to_string top1 in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu___3 uu___4);
                 (let top2 = FStar_Syntax_Util.unmeta_safe top1 in
                  let uu___2 =
                    let uu___3 = FStar_Syntax_Subst.compress top2 in
                    uu___3.FStar_Syntax_Syntax.n in
                  match uu___2 with
                  | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) ->
                      let eff_name =
                        FStar_TypeChecker_Env.norm_eff_name
                          cfg.FStar_TypeChecker_Cfg.tcenv m in
                      let ed =
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv eff_name in
                      let uu___3 =
                        let uu___4 =
                          FStar_All.pipe_right ed
                            FStar_Syntax_Util.get_eff_repr in
                        FStar_All.pipe_right uu___4 FStar_Util.must in
                      (match uu___3 with
                       | (uu___4, repr) ->
                           let uu___5 =
                             let uu___6 =
                               FStar_All.pipe_right ed
                                 FStar_Syntax_Util.get_bind_repr in
                             FStar_All.pipe_right uu___6 FStar_Util.must in
                           (match uu___5 with
                            | (uu___6, bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Pervasives.Inr uu___7 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Pervasives.Inl x ->
                                     let is_return e =
                                       let uu___7 =
                                         let uu___8 =
                                           FStar_Syntax_Subst.compress e in
                                         uu___8.FStar_Syntax_Syntax.n in
                                       match uu___7 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,
                                            FStar_Syntax_Syntax.Meta_monadic
                                            (uu___8, uu___9))
                                           ->
                                           let uu___10 =
                                             let uu___11 =
                                               FStar_Syntax_Subst.compress e1 in
                                             uu___11.FStar_Syntax_Syntax.n in
                                           (match uu___10 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,
                                                 FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu___11, msrc, uu___12))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu___13 =
                                                  FStar_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu___13
                                            | uu___11 ->
                                                FStar_Pervasives_Native.None)
                                       | uu___8 ->
                                           FStar_Pervasives_Native.None in
                                     let uu___7 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef in
                                     (match uu___7 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___8 = lb in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___8.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___8.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___8.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e;
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___8.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___8.FStar_Syntax_Syntax.lbpos)
                                            } in
                                          let uu___8 = FStar_List.tl stack1 in
                                          let uu___9 =
                                            let uu___10 =
                                              let uu___11 =
                                                let uu___12 =
                                                  FStar_Syntax_Util.mk_reify
                                                    body in
                                                ((false, [lb1]), uu___12) in
                                              FStar_Syntax_Syntax.Tm_let
                                                uu___11 in
                                            FStar_Syntax_Syntax.mk uu___10
                                              top2.FStar_Syntax_Syntax.pos in
                                          norm cfg env1 uu___8 uu___9
                                      | FStar_Pervasives_Native.None ->
                                          let uu___8 =
                                            let uu___9 = is_return body in
                                            match uu___9 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu___10;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu___11;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu___10 -> false in
                                          if uu___8
                                          then
                                            norm cfg env1 stack1
                                              lb.FStar_Syntax_Syntax.lbdef
                                          else
                                            (let rng =
                                               top2.FStar_Syntax_Syntax.pos in
                                             let head =
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Util.mk_reify
                                                 lb.FStar_Syntax_Syntax.lbdef in
                                             let body1 =
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Util.mk_reify
                                                 body in
                                             let body_rc =
                                               {
                                                 FStar_Syntax_Syntax.residual_effect
                                                   = m;
                                                 FStar_Syntax_Syntax.residual_typ
                                                   =
                                                   (FStar_Pervasives_Native.Some
                                                      t);
                                                 FStar_Syntax_Syntax.residual_flags
                                                   = []
                                               } in
                                             let body2 =
                                               let uu___10 =
                                                 let uu___11 =
                                                   let uu___12 =
                                                     let uu___13 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         x in
                                                     [uu___13] in
                                                   (uu___12, body1,
                                                     (FStar_Pervasives_Native.Some
                                                        body_rc)) in
                                                 FStar_Syntax_Syntax.Tm_abs
                                                   uu___11 in
                                               FStar_Syntax_Syntax.mk uu___10
                                                 body1.FStar_Syntax_Syntax.pos in
                                             let close =
                                               closure_as_term cfg env1 in
                                             let bind_inst =
                                               let uu___10 =
                                                 let uu___11 =
                                                   FStar_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu___11.FStar_Syntax_Syntax.n in
                                               match uu___10 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (bind,
                                                    uu___11::uu___12::[])
                                                   ->
                                                   let uu___13 =
                                                     let uu___14 =
                                                       let uu___15 =
                                                         let uu___16 =
                                                           let uu___17 =
                                                             close
                                                               lb.FStar_Syntax_Syntax.lbtyp in
                                                           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                             cfg.FStar_TypeChecker_Cfg.tcenv
                                                             uu___17 in
                                                         let uu___17 =
                                                           let uu___18 =
                                                             let uu___19 =
                                                               close t in
                                                             (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                               cfg.FStar_TypeChecker_Cfg.tcenv
                                                               uu___19 in
                                                           [uu___18] in
                                                         uu___16 :: uu___17 in
                                                       (bind, uu___15) in
                                                     FStar_Syntax_Syntax.Tm_uinst
                                                       uu___14 in
                                                   FStar_Syntax_Syntax.mk
                                                     uu___13 rng
                                               | uu___11 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let bind_inst_args f_arg =
                                               let uu___10 =
                                                 FStar_Syntax_Util.is_layered
                                                   ed in
                                               if uu___10
                                               then
                                                 let unit_args =
                                                   let uu___11 =
                                                     let uu___12 =
                                                       let uu___13 =
                                                         let uu___14 =
                                                           FStar_All.pipe_right
                                                             ed
                                                             FStar_Syntax_Util.get_bind_vc_combinator in
                                                         FStar_All.pipe_right
                                                           uu___14
                                                           FStar_Pervasives_Native.snd in
                                                       FStar_All.pipe_right
                                                         uu___13
                                                         FStar_Syntax_Subst.compress in
                                                     uu___12.FStar_Syntax_Syntax.n in
                                                   match uu___11 with
                                                   | FStar_Syntax_Syntax.Tm_arrow
                                                       (uu___12::uu___13::bs,
                                                        uu___14)
                                                       when
                                                       (FStar_List.length bs)
                                                         >=
                                                         (Prims.of_int (2))
                                                       ->
                                                       let uu___15 =
                                                         let uu___16 =
                                                           FStar_All.pipe_right
                                                             bs
                                                             (FStar_List.splitAt
                                                                ((FStar_List.length
                                                                    bs)
                                                                   -
                                                                   (Prims.of_int (2)))) in
                                                         FStar_All.pipe_right
                                                           uu___16
                                                           FStar_Pervasives_Native.fst in
                                                       FStar_All.pipe_right
                                                         uu___15
                                                         (FStar_List.map
                                                            (fun uu___16 ->
                                                               FStar_Syntax_Syntax.as_arg
                                                                 FStar_Syntax_Syntax.unit_const))
                                                   | uu___12 ->
                                                       let uu___13 =
                                                         let uu___14 =
                                                           let uu___15 =
                                                             FStar_Ident.string_of_lid
                                                               ed.FStar_Syntax_Syntax.mname in
                                                           let uu___16 =
                                                             let uu___17 =
                                                               let uu___18 =
                                                                 FStar_All.pipe_right
                                                                   ed
                                                                   FStar_Syntax_Util.get_bind_vc_combinator in
                                                               FStar_All.pipe_right
                                                                 uu___18
                                                                 FStar_Pervasives_Native.snd in
                                                             FStar_All.pipe_right
                                                               uu___17
                                                               FStar_Syntax_Print.term_to_string in
                                                           FStar_Util.format2
                                                             "bind_wp for layered effect %s is not an arrow with >= 4 arguments (%s)"
                                                             uu___15 uu___16 in
                                                         (FStar_Errors.Fatal_UnexpectedEffect,
                                                           uu___14) in
                                                       FStar_Errors.raise_error
                                                         uu___13 rng in
                                                 let uu___11 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp in
                                                 let uu___12 =
                                                   let uu___13 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t in
                                                   let uu___14 =
                                                     let uu___15 =
                                                       let uu___16 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           f_arg in
                                                       let uu___17 =
                                                         let uu___18 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             body2 in
                                                         [uu___18] in
                                                       uu___16 :: uu___17 in
                                                     FStar_List.append
                                                       unit_args uu___15 in
                                                   uu___13 :: uu___14 in
                                                 uu___11 :: uu___12
                                               else
                                                 (let maybe_range_arg =
                                                    let uu___12 =
                                                      FStar_Util.for_some
                                                        (FStar_Syntax_Util.attr_eq
                                                           FStar_Syntax_Util.dm4f_bind_range_attr)
                                                        ed.FStar_Syntax_Syntax.eff_attrs in
                                                    if uu___12
                                                    then
                                                      let uu___13 =
                                                        let uu___14 =
                                                          FStar_TypeChecker_Cfg.embed_simple
                                                            FStar_Syntax_Embeddings.e_range
                                                            lb.FStar_Syntax_Syntax.lbpos
                                                            lb.FStar_Syntax_Syntax.lbpos in
                                                        FStar_Syntax_Syntax.as_arg
                                                          uu___14 in
                                                      let uu___14 =
                                                        let uu___15 =
                                                          let uu___16 =
                                                            FStar_TypeChecker_Cfg.embed_simple
                                                              FStar_Syntax_Embeddings.e_range
                                                              body2.FStar_Syntax_Syntax.pos
                                                              body2.FStar_Syntax_Syntax.pos in
                                                          FStar_Syntax_Syntax.as_arg
                                                            uu___16 in
                                                        [uu___15] in
                                                      uu___13 :: uu___14
                                                    else [] in
                                                  let uu___12 =
                                                    let uu___13 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        lb.FStar_Syntax_Syntax.lbtyp in
                                                    let uu___14 =
                                                      let uu___15 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          t in
                                                      [uu___15] in
                                                    uu___13 :: uu___14 in
                                                  let uu___13 =
                                                    let uu___14 =
                                                      let uu___15 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          FStar_Syntax_Syntax.tun in
                                                      let uu___16 =
                                                        let uu___17 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            f_arg in
                                                        let uu___18 =
                                                          let uu___19 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.tun in
                                                          let uu___20 =
                                                            let uu___21 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                body2 in
                                                            [uu___21] in
                                                          uu___19 :: uu___20 in
                                                        uu___17 :: uu___18 in
                                                      uu___15 :: uu___16 in
                                                    FStar_List.append
                                                      maybe_range_arg uu___14 in
                                                  FStar_List.append uu___12
                                                    uu___13) in
                                             let reified =
                                               let is_total_effect =
                                                 FStar_TypeChecker_Env.is_total_effect
                                                   cfg.FStar_TypeChecker_Cfg.tcenv
                                                   eff_name in
                                               if is_total_effect
                                               then
                                                 let uu___10 =
                                                   let uu___11 =
                                                     let uu___12 =
                                                       bind_inst_args head in
                                                     (bind_inst, uu___12) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu___11 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu___10 rng
                                               else
                                                 (let uu___11 =
                                                    let bv =
                                                      FStar_Syntax_Syntax.new_bv
                                                        FStar_Pervasives_Native.None
                                                        x.FStar_Syntax_Syntax.sort in
                                                    let lb1 =
                                                      let uu___12 =
                                                        let uu___13 =
                                                          let uu___14 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              x.FStar_Syntax_Syntax.sort in
                                                          [uu___14] in
                                                        FStar_Syntax_Util.mk_app
                                                          repr uu___13 in
                                                      {
                                                        FStar_Syntax_Syntax.lbname
                                                          =
                                                          (FStar_Pervasives.Inl
                                                             bv);
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = [];
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu___12;
                                                        FStar_Syntax_Syntax.lbeff
                                                          =
                                                          (if is_total_effect
                                                           then
                                                             FStar_Parser_Const.effect_Tot_lid
                                                           else
                                                             FStar_Parser_Const.effect_Dv_lid);
                                                        FStar_Syntax_Syntax.lbdef
                                                          = head;
                                                        FStar_Syntax_Syntax.lbattrs
                                                          = [];
                                                        FStar_Syntax_Syntax.lbpos
                                                          =
                                                          (head.FStar_Syntax_Syntax.pos)
                                                      } in
                                                    let uu___12 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        bv in
                                                    (lb1, bv, uu___12) in
                                                  match uu___11 with
                                                  | (lb_head, head_bv, head1)
                                                      ->
                                                      let uu___12 =
                                                        let uu___13 =
                                                          let uu___14 =
                                                            let uu___15 =
                                                              let uu___16 =
                                                                let uu___17 =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    head_bv in
                                                                [uu___17] in
                                                              FStar_Syntax_Subst.close
                                                                uu___16 in
                                                            let uu___16 =
                                                              let uu___17 =
                                                                let uu___18 =
                                                                  let uu___19
                                                                    =
                                                                    bind_inst_args
                                                                    head1 in
                                                                  (bind_inst,
                                                                    uu___19) in
                                                                FStar_Syntax_Syntax.Tm_app
                                                                  uu___18 in
                                                              FStar_Syntax_Syntax.mk
                                                                uu___17 rng in
                                                            FStar_All.pipe_left
                                                              uu___15 uu___16 in
                                                          ((false, [lb_head]),
                                                            uu___14) in
                                                        FStar_Syntax_Syntax.Tm_let
                                                          uu___13 in
                                                      FStar_Syntax_Syntax.mk
                                                        uu___12 rng) in
                                             FStar_TypeChecker_Cfg.log cfg
                                               (fun uu___11 ->
                                                  let uu___12 =
                                                    FStar_Syntax_Print.term_to_string
                                                      top0 in
                                                  let uu___13 =
                                                    FStar_Syntax_Print.term_to_string
                                                      reified in
                                                  FStar_Util.print2
                                                    "Reified (1) <%s> to %s\n"
                                                    uu___12 uu___13);
                                             (let uu___11 =
                                                FStar_List.tl stack1 in
                                              norm cfg env1 uu___11 reified))))))
                  | FStar_Syntax_Syntax.Tm_app (head, args) ->
                      ((let uu___4 = FStar_Options.defensive () in
                        if uu___4
                        then
                          let is_arg_impure uu___5 =
                            match uu___5 with
                            | (e, q) ->
                                let uu___6 =
                                  let uu___7 = FStar_Syntax_Subst.compress e in
                                  uu___7.FStar_Syntax_Syntax.n in
                                (match uu___6 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,
                                      FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1, m2, t'))
                                     ->
                                     let uu___7 =
                                       FStar_Syntax_Util.is_pure_effect m1 in
                                     Prims.op_Negation uu___7
                                 | uu___7 -> false) in
                          let uu___5 =
                            let uu___6 =
                              let uu___7 = FStar_Syntax_Syntax.as_arg head in
                              uu___7 :: args in
                            FStar_Util.for_some is_arg_impure uu___6 in
                          (if uu___5
                           then
                             let uu___6 =
                               let uu___7 =
                                 let uu___8 =
                                   FStar_Syntax_Print.term_to_string top2 in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu___8 in
                               (FStar_Errors.Warning_Defensive, uu___7) in
                             FStar_Errors.log_issue
                               top2.FStar_Syntax_Syntax.pos uu___6
                           else ())
                        else ());
                       (let fallback1 uu___4 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu___6 ->
                               let uu___7 =
                                 FStar_Syntax_Print.term_to_string top0 in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu___7 "");
                          (let uu___6 = FStar_List.tl stack1 in
                           let uu___7 = FStar_Syntax_Util.mk_reify top2 in
                           norm cfg env1 uu___6 uu___7) in
                        let fallback2 uu___4 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu___6 ->
                               let uu___7 =
                                 FStar_Syntax_Print.term_to_string top0 in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu___7 "");
                          (let uu___6 = FStar_List.tl stack1 in
                           let uu___7 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (top2,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               top0.FStar_Syntax_Syntax.pos in
                           norm cfg env1 uu___6 uu___7) in
                        let uu___4 =
                          let uu___5 = FStar_Syntax_Util.un_uinst head in
                          uu___5.FStar_Syntax_Syntax.n in
                        match uu___4 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid in
                            let uu___5 =
                              let uu___6 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid in
                              Prims.op_Negation uu___6 in
                            if uu___5
                            then fallback1 ()
                            else
                              (let uu___7 =
                                 let uu___8 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo in
                                 FStar_Option.isNone uu___8 in
                               if uu___7
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu___9 =
                                      FStar_Syntax_Util.mk_reify head in
                                    FStar_Syntax_Syntax.mk_Tm_app uu___9 args
                                      t.FStar_Syntax_Syntax.pos in
                                  let uu___9 = FStar_List.tl stack1 in
                                  norm cfg env1 uu___9 t1))
                        | uu___5 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e, FStar_Syntax_Syntax.Meta_monadic uu___3) ->
                      do_reify_monadic fallback cfg env1 stack1 e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e, FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc, mtgt, t'))
                      ->
                      let lifted =
                        let uu___3 = closure_as_term cfg env1 t' in
                        reify_lift cfg e msrc mtgt uu___3 in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu___4 ->
                            let uu___5 =
                              FStar_Syntax_Print.term_to_string lifted in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu___5);
                       (let uu___4 = FStar_List.tl stack1 in
                        norm cfg env1 uu___4 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e, asc_opt, branches1) ->
                      let branches2 =
                        FStar_All.pipe_right branches1
                          (FStar_List.map
                             (fun uu___3 ->
                                match uu___3 with
                                | (pat, wopt, tm) ->
                                    let uu___4 =
                                      FStar_Syntax_Util.mk_reify tm in
                                    (pat, wopt, uu___4))) in
                      let tm =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_match
                             (e, asc_opt, branches2))
                          top2.FStar_Syntax_Syntax.pos in
                      let uu___3 = FStar_List.tl stack1 in
                      norm cfg env1 uu___3 tm
                  | uu___3 -> fallback ()))
and (reify_lift :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.monad_name ->
        FStar_Syntax_Syntax.monad_name ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun e ->
      fun msrc ->
        fun mtgt ->
          fun t ->
            let env1 = cfg.FStar_TypeChecker_Cfg.tcenv in
            FStar_TypeChecker_Cfg.log cfg
              (fun uu___1 ->
                 let uu___2 = FStar_Ident.string_of_lid msrc in
                 let uu___3 = FStar_Ident.string_of_lid mtgt in
                 let uu___4 = FStar_Syntax_Print.term_to_string e in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu___2
                   uu___3 uu___4);
            (let uu___1 =
               ((FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc))
                 &&
                 (let uu___2 =
                    FStar_All.pipe_right mtgt
                      (FStar_TypeChecker_Env.is_layered_effect env1) in
                  Prims.op_Negation uu___2) in
             if uu___1
             then
               let ed =
                 let uu___2 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt in
                 FStar_TypeChecker_Env.get_effect_decl env1 uu___2 in
               let uu___2 =
                 let uu___3 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr in
                 FStar_All.pipe_right uu___3 FStar_Util.must in
               match uu___2 with
               | (uu___3, repr) ->
                   let uu___4 =
                     let uu___5 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_return_repr in
                     FStar_All.pipe_right uu___5 FStar_Util.must in
                   (match uu___4 with
                    | (uu___5, return_repr) ->
                        let return_inst =
                          let uu___6 =
                            let uu___7 =
                              FStar_Syntax_Subst.compress return_repr in
                            uu___7.FStar_Syntax_Syntax.n in
                          match uu___6 with
                          | FStar_Syntax_Syntax.Tm_uinst
                              (return_tm, uu___7::[]) ->
                              let uu___8 =
                                let uu___9 =
                                  let uu___10 =
                                    let uu___11 =
                                      env1.FStar_TypeChecker_Env.universe_of
                                        env1 t in
                                    [uu___11] in
                                  (return_tm, uu___10) in
                                FStar_Syntax_Syntax.Tm_uinst uu___9 in
                              FStar_Syntax_Syntax.mk uu___8
                                e.FStar_Syntax_Syntax.pos
                          | uu___7 ->
                              failwith "NIY : Reification of indexed effects" in
                        let uu___6 =
                          let bv =
                            FStar_Syntax_Syntax.new_bv
                              FStar_Pervasives_Native.None t in
                          let lb =
                            let uu___7 =
                              let uu___8 =
                                let uu___9 = FStar_Syntax_Syntax.as_arg t in
                                [uu___9] in
                              FStar_Syntax_Util.mk_app repr uu___8 in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (FStar_Pervasives.Inl bv);
                              FStar_Syntax_Syntax.lbunivs = [];
                              FStar_Syntax_Syntax.lbtyp = uu___7;
                              FStar_Syntax_Syntax.lbeff = msrc;
                              FStar_Syntax_Syntax.lbdef = e;
                              FStar_Syntax_Syntax.lbattrs = [];
                              FStar_Syntax_Syntax.lbpos =
                                (e.FStar_Syntax_Syntax.pos)
                            } in
                          let uu___7 = FStar_Syntax_Syntax.bv_to_name bv in
                          (lb, bv, uu___7) in
                        (match uu___6 with
                         | (lb_e, e_bv, e1) ->
                             let uu___7 =
                               let uu___8 =
                                 let uu___9 =
                                   let uu___10 =
                                     let uu___11 =
                                       let uu___12 =
                                         FStar_Syntax_Syntax.mk_binder e_bv in
                                       [uu___12] in
                                     FStar_Syntax_Subst.close uu___11 in
                                   let uu___11 =
                                     let uu___12 =
                                       let uu___13 =
                                         let uu___14 =
                                           let uu___15 =
                                             FStar_Syntax_Syntax.as_arg t in
                                           let uu___16 =
                                             let uu___17 =
                                               FStar_Syntax_Syntax.as_arg e1 in
                                             [uu___17] in
                                           uu___15 :: uu___16 in
                                         (return_inst, uu___14) in
                                       FStar_Syntax_Syntax.Tm_app uu___13 in
                                     FStar_Syntax_Syntax.mk uu___12
                                       e1.FStar_Syntax_Syntax.pos in
                                   FStar_All.pipe_left uu___10 uu___11 in
                                 ((false, [lb_e]), uu___9) in
                               FStar_Syntax_Syntax.Tm_let uu___8 in
                             FStar_Syntax_Syntax.mk uu___7
                               e1.FStar_Syntax_Syntax.pos))
             else
               (let uu___3 = FStar_TypeChecker_Env.monad_leq env1 msrc mtgt in
                match uu___3 with
                | FStar_Pervasives_Native.None ->
                    let uu___4 =
                      let uu___5 = FStar_Ident.string_of_lid msrc in
                      let uu___6 = FStar_Ident.string_of_lid mtgt in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu___5 uu___6 in
                    failwith uu___4
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu___4;
                      FStar_TypeChecker_Env.mtarget = uu___5;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu___6;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None;_};_}
                    ->
                    let uu___7 =
                      let uu___8 = FStar_Ident.string_of_lid msrc in
                      let uu___9 = FStar_Ident.string_of_lid mtgt in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu___8 uu___9 in
                    failwith uu___7
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu___4;
                      FStar_TypeChecker_Env.mtarget = uu___5;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu___6;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let e1 =
                      let uu___7 =
                        FStar_TypeChecker_Env.is_reifiable_effect env1 msrc in
                      if uu___7
                      then FStar_Syntax_Util.mk_reify e
                      else
                        (let uu___9 =
                           let uu___10 =
                             let uu___11 =
                               let uu___12 =
                                 FStar_Syntax_Syntax.null_binder
                                   FStar_Syntax_Syntax.t_unit in
                               [uu___12] in
                             (uu___11, e,
                               (FStar_Pervasives_Native.Some
                                  {
                                    FStar_Syntax_Syntax.residual_effect =
                                      msrc;
                                    FStar_Syntax_Syntax.residual_typ =
                                      (FStar_Pervasives_Native.Some t);
                                    FStar_Syntax_Syntax.residual_flags = []
                                  })) in
                           FStar_Syntax_Syntax.Tm_abs uu___10 in
                         FStar_Syntax_Syntax.mk uu___9
                           e.FStar_Syntax_Syntax.pos) in
                    let uu___7 =
                      env1.FStar_TypeChecker_Env.universe_of env1 t in
                    lift uu___7 t e1))
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
  fun cfg ->
    fun env1 ->
      fun args ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu___ ->
                   match uu___ with
                   | (a, imp) ->
                       let uu___1 = norm cfg env1 [] a in (uu___1, imp))))
and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg ->
    fun env1 ->
      fun comp ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu___1 ->
             let uu___2 = FStar_Syntax_Print.comp_to_string comp in
             let uu___3 = FStar_Util.string_of_int (FStar_List.length env1) in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements\n"
               uu___2 uu___3);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t, uopt) ->
             let t1 = norm cfg env1 [] t in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu___1 = norm_universe cfg env1 u in
                   FStar_All.pipe_left
                     (fun uu___2 -> FStar_Pervasives_Native.Some uu___2)
                     uu___1
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
             let uu___1 = comp in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos = (uu___1.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars = (uu___1.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t, uopt) ->
             let t1 = norm cfg env1 [] t in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu___1 = norm_universe cfg env1 u in
                   FStar_All.pipe_left
                     (fun uu___2 -> FStar_Pervasives_Native.Some uu___2)
                     uu___1
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
             let uu___1 = comp in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos = (uu___1.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars = (uu___1.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let effect_args =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                 (if
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                  then
                    FStar_List.map
                      (fun uu___1 ->
                         FStar_All.pipe_right FStar_Syntax_Syntax.unit_const
                           FStar_Syntax_Syntax.as_arg)
                  else
                    FStar_List.mapi
                      (fun idx ->
                         fun uu___2 ->
                           match uu___2 with
                           | (a, i) ->
                               let uu___3 = norm cfg env1 [] a in (uu___3, i))) in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___1 ->
                       match uu___1 with
                       | FStar_Syntax_Syntax.DECREASES
                           (FStar_Syntax_Syntax.Decreases_lex l) ->
                           let uu___2 =
                             let uu___3 =
                               FStar_All.pipe_right l
                                 (FStar_List.map (norm cfg env1 [])) in
                             FStar_All.pipe_right uu___3
                               (fun uu___4 ->
                                  FStar_Syntax_Syntax.Decreases_lex uu___4) in
                           FStar_Syntax_Syntax.DECREASES uu___2
                       | FStar_Syntax_Syntax.DECREASES
                           (FStar_Syntax_Syntax.Decreases_wf (rel, e)) ->
                           let uu___2 =
                             let uu___3 =
                               let uu___4 = norm cfg env1 [] rel in
                               let uu___5 = norm cfg env1 [] e in
                               (uu___4, uu___5) in
                             FStar_Syntax_Syntax.Decreases_wf uu___3 in
                           FStar_Syntax_Syntax.DECREASES uu___2
                       | f -> f)) in
             let comp_univs =
               FStar_List.map (norm_universe cfg env1)
                 ct.FStar_Syntax_Syntax.comp_univs in
             let result_typ =
               norm cfg env1 [] ct.FStar_Syntax_Syntax.result_typ in
             let uu___1 = comp in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2 = ct in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos = (uu___1.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars = (uu___1.FStar_Syntax_Syntax.vars)
             })
and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg ->
    fun env1 ->
      fun b ->
        let x =
          let uu___ = b.FStar_Syntax_Syntax.binder_bv in
          let uu___1 =
            norm cfg env1 []
              (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
          {
            FStar_Syntax_Syntax.ppname = (uu___.FStar_Syntax_Syntax.ppname);
            FStar_Syntax_Syntax.index = (uu___.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort = uu___1
          } in
        let imp =
          match b.FStar_Syntax_Syntax.binder_qual with
          | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
              let uu___ =
                let uu___1 = closure_as_term cfg env1 t in
                FStar_Syntax_Syntax.Meta uu___1 in
              FStar_Pervasives_Native.Some uu___
          | i -> i in
        let attrs =
          FStar_List.map (norm cfg env1 [])
            b.FStar_Syntax_Syntax.binder_attrs in
        FStar_Syntax_Syntax.mk_binder_with_attrs x imp attrs
and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg ->
    fun env1 ->
      fun bs ->
        let uu___ =
          FStar_List.fold_left
            (fun uu___1 ->
               fun b ->
                 match uu___1 with
                 | (nbs', env2) ->
                     let b1 = norm_binder cfg env2 b in
                     ((b1 :: nbs'), (dummy :: env2))) ([], env1) bs in
        match uu___ with | (nbs, uu___1) -> FStar_List.rev nbs
and (norm_lcomp_opt :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun cfg ->
    fun env1 ->
      fun lopt ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags =
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags in
            let uu___ =
              let uu___1 = rc in
              let uu___2 =
                if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                then FStar_Pervasives_Native.None
                else
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (norm cfg env1 []) in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___1.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu___2;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___1.FStar_Syntax_Syntax.residual_flags)
              } in
            FStar_Pervasives_Native.Some uu___
        | uu___ -> lopt
and (maybe_simplify :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun tm ->
          let tm' = maybe_simplify_aux cfg env1 stack1 tm in
          if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.b380
          then
            (let uu___1 = FStar_Syntax_Print.term_to_string tm in
             let uu___2 = FStar_Syntax_Print.term_to_string tm' in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu___1 uu___2)
          else ();
          tm'
and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg ->
    fun uu___ ->
      match uu___ with
      | FStar_Pervasives.Inr x -> norm cfg [] [] x
      | FStar_Pervasives.Inl l ->
          let uu___1 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l in
          (match uu___1 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None ->
               let uu___2 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None in
               FStar_Syntax_Syntax.fv_to_tm uu___2)
and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun tm ->
          let tm1 =
            let uu___ = norm_cb cfg in reduce_primops uu___ cfg env1 tm in
          let uu___ =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify in
          if uu___
          then tm1
          else
            (let w t =
               let uu___2 = t in
               {
                 FStar_Syntax_Syntax.n = (uu___2.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars = (uu___2.FStar_Syntax_Syntax.vars)
               } in
             let simp_t t =
               let uu___2 =
                 let uu___3 = FStar_Syntax_Util.unmeta t in
                 uu___3.FStar_Syntax_Syntax.n in
               match uu___2 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu___3 -> FStar_Pervasives_Native.None in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t, uu___2)::args1, b::bs1) ->
                   let uu___3 =
                     let uu___4 = FStar_Syntax_Subst.compress t in
                     uu___4.FStar_Syntax_Syntax.n in
                   (match uu___3 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq
                           b.FStar_Syntax_Syntax.binder_bv bv')
                          && (args_are_binders args1 bs1)
                    | uu___4 -> false)
               | ([], []) -> true
               | (uu___2, uu___3) -> false in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu___3 = FStar_Syntax_Print.term_to_string t in
                  let uu___4 = FStar_Syntax_Print.tag_of_term t in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu___3
                    uu___4)
               else ();
               (let uu___3 = FStar_Syntax_Util.head_and_args_full t in
                match uu___3 with
                | (hd, args) ->
                    let uu___4 =
                      let uu___5 = FStar_Syntax_Subst.compress hd in
                      uu___5.FStar_Syntax_Syntax.n in
                    (match uu___4 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu___6 = FStar_Syntax_Print.term_to_string t in
                             let uu___7 = FStar_Syntax_Print.bv_to_string bv in
                             let uu___8 =
                               FStar_Syntax_Print.term_to_string hd in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu___6 uu___7 uu___8)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu___5 -> FStar_Pervasives_Native.None)) in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu___3 = FStar_Syntax_Print.term_to_string t in
                  let uu___4 = FStar_Syntax_Print.tag_of_term t in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu___3 uu___4)
               else ();
               (let uu___3 = FStar_Syntax_Util.is_squash t in
                match uu___3 with
                | FStar_Pervasives_Native.Some (uu___4, t') ->
                    is_applied bs t'
                | uu___4 ->
                    let uu___5 = FStar_Syntax_Util.is_auto_squash t in
                    (match uu___5 with
                     | FStar_Pervasives_Native.Some (uu___6, t') ->
                         is_applied bs t'
                     | uu___6 -> is_applied bs t)) in
             let is_quantified_const bv phi =
               let uu___2 = FStar_Syntax_Util.destruct_typ_as_formula phi in
               match uu___2 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid, (p, uu___3)::(q, uu___4)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu___6 = FStar_Syntax_Print.term_to_string p in
                       let uu___7 = FStar_Syntax_Print.term_to_string q in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n" uu___6
                         uu___7)
                    else ();
                    (let uu___6 = FStar_Syntax_Util.destruct_typ_as_formula p in
                     match uu___6 with
                     | FStar_Pervasives_Native.None ->
                         let uu___7 =
                           let uu___8 = FStar_Syntax_Subst.compress p in
                           uu___8.FStar_Syntax_Syntax.n in
                         (match uu___7 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu___9 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q in
                                FStar_Pervasives_Native.Some uu___9))
                          | uu___8 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1, (p1, uu___7)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu___8 =
                           let uu___9 = FStar_Syntax_Subst.compress p1 in
                           uu___9.FStar_Syntax_Syntax.n in
                         (match uu___8 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu___10 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q in
                                FStar_Pervasives_Native.Some uu___10))
                          | uu___9 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs, pats, phi1)) ->
                         let uu___7 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1 in
                         (match uu___7 with
                          | FStar_Pervasives_Native.None ->
                              let uu___8 = is_applied_maybe_squashed bs phi1 in
                              (match uu___8 with
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
                                               FStar_Syntax_Util.ktype0)) in
                                     let uu___10 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q in
                                     FStar_Pervasives_Native.Some uu___10))
                               | uu___9 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1, (p1, uu___8)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu___9 = is_applied_maybe_squashed bs p1 in
                              (match uu___9 with
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
                                               FStar_Syntax_Util.ktype0)) in
                                     let uu___11 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q in
                                     FStar_Pervasives_Native.Some uu___11))
                               | uu___10 -> FStar_Pervasives_Native.None)
                          | uu___8 -> FStar_Pervasives_Native.None)
                     | uu___7 -> FStar_Pervasives_Native.None))
               | uu___3 -> FStar_Pervasives_Native.None in
             let is_forall_const phi =
               let uu___2 = FStar_Syntax_Util.destruct_typ_as_formula phi in
               match uu___2 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   (b::[], uu___3, phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu___5 =
                         FStar_Syntax_Print.bv_to_string
                           b.FStar_Syntax_Syntax.binder_bv in
                       let uu___6 = FStar_Syntax_Print.term_to_string phi' in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu___5 uu___6)
                    else ();
                    is_quantified_const b.FStar_Syntax_Syntax.binder_bv phi')
               | uu___3 -> FStar_Pervasives_Native.None in
             let is_const_match phi =
               let uu___2 =
                 let uu___3 = FStar_Syntax_Subst.compress phi in
                 uu___3.FStar_Syntax_Syntax.n in
               match uu___2 with
               | FStar_Syntax_Syntax.Tm_match (uu___3, uu___4, br::brs) ->
                   let uu___5 = br in
                   (match uu___5 with
                    | (uu___6, uu___7, e) ->
                        let r =
                          let uu___8 = simp_t e in
                          match uu___8 with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu___9 =
                                FStar_List.for_all
                                  (fun uu___10 ->
                                     match uu___10 with
                                     | (uu___11, uu___12, e') ->
                                         let uu___13 = simp_t e' in
                                         uu___13 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs in
                              if uu___9
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None in
                        r)
               | uu___3 -> FStar_Pervasives_Native.None in
             let maybe_auto_squash t =
               let uu___2 = FStar_Syntax_Util.is_sub_singleton t in
               if uu___2
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu___2 =
                 match uu___2 with
                 | (t1, q) ->
                     let uu___3 = FStar_Syntax_Util.is_auto_squash t1 in
                     (match uu___3 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero, t2) -> (t2, q)
                      | uu___4 -> (t1, q)) in
               let uu___2 = FStar_Syntax_Util.head_and_args t in
               match uu___2 with
               | (head, args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args in
                   FStar_Syntax_Syntax.mk_Tm_app head args1
                     t.FStar_Syntax_Syntax.pos in
             let rec clearly_inhabited ty =
               let uu___2 =
                 let uu___3 = FStar_Syntax_Util.unmeta ty in
                 uu___3.FStar_Syntax_Syntax.n in
               match uu___2 with
               | FStar_Syntax_Syntax.Tm_uinst (t, uu___3) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu___3, c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu___3 -> false in
             let simplify arg =
               let uu___2 = simp_t (FStar_Pervasives_Native.fst arg) in
               (uu___2, arg) in
             let uu___2 = is_forall_const tm1 in
             match uu___2 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu___4 = FStar_Syntax_Print.term_to_string tm1 in
                     let uu___5 = FStar_Syntax_Print.term_to_string tm' in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu___4 uu___5)
                  else ();
                  (let uu___4 = norm cfg env1 [] tm' in
                   maybe_simplify_aux cfg env1 stack1 uu___4))
             | FStar_Pervasives_Native.None ->
                 let uu___3 =
                   let uu___4 = FStar_Syntax_Subst.compress tm1 in
                   uu___4.FStar_Syntax_Syntax.n in
                 (match uu___3 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu___4;
                              FStar_Syntax_Syntax.vars = uu___5;_},
                            uu___6);
                         FStar_Syntax_Syntax.pos = uu___7;
                         FStar_Syntax_Syntax.vars = uu___8;_},
                       args)
                      ->
                      let uu___9 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid in
                      if uu___9
                      then
                        let uu___10 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        (match uu___10 with
                         | (FStar_Pervasives_Native.Some (true), uu___11)::
                             (uu___12, (arg, uu___13))::[] ->
                             maybe_auto_squash arg
                         | (uu___11, (arg, uu___12))::(FStar_Pervasives_Native.Some
                                                       (true), uu___13)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false), uu___11)::uu___12::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu___11::(FStar_Pervasives_Native.Some (false),
                                     uu___12)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu___11 -> squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu___11 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid in
                         if uu___11
                         then
                           let uu___12 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify) in
                           match uu___12 with
                           | (FStar_Pervasives_Native.Some (true), uu___13)::uu___14::[]
                               -> w FStar_Syntax_Util.t_true
                           | uu___13::(FStar_Pervasives_Native.Some (true),
                                       uu___14)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false), uu___13)::
                               (uu___14, (arg, uu___15))::[] ->
                               maybe_auto_squash arg
                           | (uu___13, (arg, uu___14))::(FStar_Pervasives_Native.Some
                                                         (false), uu___15)::[]
                               -> maybe_auto_squash arg
                           | uu___13 -> squashed_head_un_auto_squash_args tm1
                         else
                           (let uu___13 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid in
                            if uu___13
                            then
                              let uu___14 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify) in
                              match uu___14 with
                              | uu___15::(FStar_Pervasives_Native.Some
                                          (true), uu___16)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false),
                                 uu___15)::uu___16::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true),
                                 uu___15)::(uu___16, (arg, uu___17))::[] ->
                                  maybe_auto_squash arg
                              | (uu___15, (p, uu___16))::(uu___17,
                                                          (q, uu___18))::[]
                                  ->
                                  let uu___19 = FStar_Syntax_Util.term_eq p q in
                                  (if uu___19
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu___15 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu___15 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid in
                               if uu___15
                               then
                                 let uu___16 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify) in
                                 match uu___16 with
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu___17)::(FStar_Pervasives_Native.Some
                                               (true), uu___18)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu___17)::(FStar_Pervasives_Native.Some
                                               (false), uu___18)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu___17)::(FStar_Pervasives_Native.Some
                                               (false), uu___18)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu___17)::(FStar_Pervasives_Native.Some
                                               (true), uu___18)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu___17, (arg, uu___18))::(FStar_Pervasives_Native.Some
                                                               (true),
                                                               uu___19)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu___17)::(uu___18, (arg, uu___19))::[]
                                     -> maybe_auto_squash arg
                                 | (uu___17, (arg, uu___18))::(FStar_Pervasives_Native.Some
                                                               (false),
                                                               uu___19)::[]
                                     ->
                                     let uu___20 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu___20
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu___17)::(uu___18, (arg, uu___19))::[]
                                     ->
                                     let uu___20 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu___20
                                 | (uu___17, (p, uu___18))::(uu___19,
                                                             (q, uu___20))::[]
                                     ->
                                     let uu___21 =
                                       FStar_Syntax_Util.term_eq p q in
                                     (if uu___21
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu___17 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu___17 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid in
                                  if uu___17
                                  then
                                    let uu___18 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify) in
                                    match uu___18 with
                                    | (FStar_Pervasives_Native.Some (true),
                                       uu___19)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false),
                                       uu___19)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu___19 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu___19 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid in
                                     if uu___19
                                     then
                                       match args with
                                       | (t, uu___20)::[] ->
                                           let uu___21 =
                                             let uu___22 =
                                               FStar_Syntax_Subst.compress t in
                                             uu___22.FStar_Syntax_Syntax.n in
                                           (match uu___21 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu___22::[], body, uu___23)
                                                ->
                                                let uu___24 = simp_t body in
                                                (match uu___24 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu___25 -> tm1)
                                            | uu___22 -> tm1)
                                       | (ty, FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu___20))::(t, uu___21)::[] ->
                                           let uu___22 =
                                             let uu___23 =
                                               FStar_Syntax_Subst.compress t in
                                             uu___23.FStar_Syntax_Syntax.n in
                                           (match uu___22 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu___23::[], body, uu___24)
                                                ->
                                                let uu___25 = simp_t body in
                                                (match uu___25 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu___26 -> tm1)
                                            | uu___23 -> tm1)
                                       | uu___20 -> tm1
                                     else
                                       (let uu___21 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid in
                                        if uu___21
                                        then
                                          match args with
                                          | (t, uu___22)::[] ->
                                              let uu___23 =
                                                let uu___24 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu___24.FStar_Syntax_Syntax.n in
                                              (match uu___23 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu___24::[], body,
                                                    uu___25)
                                                   ->
                                                   let uu___26 = simp_t body in
                                                   (match uu___26 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu___27 -> tm1)
                                               | uu___24 -> tm1)
                                          | (ty, FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu___22))::(t, uu___23)::[] ->
                                              let uu___24 =
                                                let uu___25 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu___25.FStar_Syntax_Syntax.n in
                                              (match uu___24 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu___25::[], body,
                                                    uu___26)
                                                   ->
                                                   let uu___27 = simp_t body in
                                                   (match uu___27 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | FStar_Pervasives_Native.Some
                                                        (true) when
                                                        clearly_inhabited ty
                                                        ->
                                                        w
                                                          FStar_Syntax_Util.t_true
                                                    | uu___28 -> tm1)
                                               | uu___25 -> tm1)
                                          | uu___22 -> tm1
                                        else
                                          (let uu___23 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid in
                                           if uu___23
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu___24;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu___25;_},
                                                uu___26)::[] ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu___24;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu___25;_},
                                                uu___26)::[] ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu___24 -> tm1
                                           else
                                             (let uu___25 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid in
                                              if uu___25
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid] in
                                                  let uu___26 =
                                                    let uu___27 =
                                                      FStar_Syntax_Subst.compress
                                                        t in
                                                    uu___27.FStar_Syntax_Syntax.n in
                                                  match uu___26 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu___27 -> false in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu___26 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd in
                                                     FStar_All.pipe_right
                                                       uu___26
                                                       FStar_Pervasives_Native.fst in
                                                   let uu___26 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure in
                                                   (if uu___26
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu___28 =
                                                         let uu___29 =
                                                           FStar_Syntax_Subst.compress
                                                             t in
                                                         uu___29.FStar_Syntax_Syntax.n in
                                                       match uu___28 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu___29 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t in
                                                           let uu___30 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure in
                                                           if uu___30
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu___32 =
                                                                  let uu___33
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1 in
                                                                  uu___33.FStar_Syntax_Syntax.n in
                                                                match uu___32
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd,
                                                                    uu___33)
                                                                    -> hd
                                                                | uu___33 ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app" in
                                                              let uu___32 =
                                                                let uu___33 =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg in
                                                                [uu___33] in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu___32)
                                                       | uu___29 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu___27 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1 in
                                                 match uu___27 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero,
                                                      t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu___28 ->
                                                     let uu___29 =
                                                       norm_cb cfg in
                                                     reduce_equality uu___29
                                                       cfg env1 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu___4;
                         FStar_Syntax_Syntax.vars = uu___5;_},
                       args)
                      ->
                      let uu___6 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid in
                      if uu___6
                      then
                        let uu___7 =
                          FStar_All.pipe_right args (FStar_List.map simplify) in
                        (match uu___7 with
                         | (FStar_Pervasives_Native.Some (true), uu___8)::
                             (uu___9, (arg, uu___10))::[] ->
                             maybe_auto_squash arg
                         | (uu___8, (arg, uu___9))::(FStar_Pervasives_Native.Some
                                                     (true), uu___10)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false), uu___8)::uu___9::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu___8::(FStar_Pervasives_Native.Some (false),
                                    uu___9)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu___8 -> squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu___8 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid in
                         if uu___8
                         then
                           let uu___9 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify) in
                           match uu___9 with
                           | (FStar_Pervasives_Native.Some (true), uu___10)::uu___11::[]
                               -> w FStar_Syntax_Util.t_true
                           | uu___10::(FStar_Pervasives_Native.Some (true),
                                       uu___11)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false), uu___10)::
                               (uu___11, (arg, uu___12))::[] ->
                               maybe_auto_squash arg
                           | (uu___10, (arg, uu___11))::(FStar_Pervasives_Native.Some
                                                         (false), uu___12)::[]
                               -> maybe_auto_squash arg
                           | uu___10 -> squashed_head_un_auto_squash_args tm1
                         else
                           (let uu___10 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid in
                            if uu___10
                            then
                              let uu___11 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify) in
                              match uu___11 with
                              | uu___12::(FStar_Pervasives_Native.Some
                                          (true), uu___13)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false),
                                 uu___12)::uu___13::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true),
                                 uu___12)::(uu___13, (arg, uu___14))::[] ->
                                  maybe_auto_squash arg
                              | (uu___12, (p, uu___13))::(uu___14,
                                                          (q, uu___15))::[]
                                  ->
                                  let uu___16 = FStar_Syntax_Util.term_eq p q in
                                  (if uu___16
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu___12 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu___12 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid in
                               if uu___12
                               then
                                 let uu___13 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify) in
                                 match uu___13 with
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu___14)::(FStar_Pervasives_Native.Some
                                               (true), uu___15)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu___14)::(FStar_Pervasives_Native.Some
                                               (false), uu___15)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu___14)::(FStar_Pervasives_Native.Some
                                               (false), uu___15)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu___14)::(FStar_Pervasives_Native.Some
                                               (true), uu___15)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu___14, (arg, uu___15))::(FStar_Pervasives_Native.Some
                                                               (true),
                                                               uu___16)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true),
                                    uu___14)::(uu___15, (arg, uu___16))::[]
                                     -> maybe_auto_squash arg
                                 | (uu___14, (arg, uu___15))::(FStar_Pervasives_Native.Some
                                                               (false),
                                                               uu___16)::[]
                                     ->
                                     let uu___17 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu___17
                                 | (FStar_Pervasives_Native.Some (false),
                                    uu___14)::(uu___15, (arg, uu___16))::[]
                                     ->
                                     let uu___17 =
                                       FStar_Syntax_Util.mk_neg arg in
                                     maybe_auto_squash uu___17
                                 | (uu___14, (p, uu___15))::(uu___16,
                                                             (q, uu___17))::[]
                                     ->
                                     let uu___18 =
                                       FStar_Syntax_Util.term_eq p q in
                                     (if uu___18
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu___14 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu___14 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid in
                                  if uu___14
                                  then
                                    let uu___15 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify) in
                                    match uu___15 with
                                    | (FStar_Pervasives_Native.Some (true),
                                       uu___16)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false),
                                       uu___16)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu___16 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu___16 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid in
                                     if uu___16
                                     then
                                       match args with
                                       | (t, uu___17)::[] ->
                                           let uu___18 =
                                             let uu___19 =
                                               FStar_Syntax_Subst.compress t in
                                             uu___19.FStar_Syntax_Syntax.n in
                                           (match uu___18 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu___19::[], body, uu___20)
                                                ->
                                                let uu___21 = simp_t body in
                                                (match uu___21 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu___22 -> tm1)
                                            | uu___19 -> tm1)
                                       | (ty, FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu___17))::(t, uu___18)::[] ->
                                           let uu___19 =
                                             let uu___20 =
                                               FStar_Syntax_Subst.compress t in
                                             uu___20.FStar_Syntax_Syntax.n in
                                           (match uu___19 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu___20::[], body, uu___21)
                                                ->
                                                let uu___22 = simp_t body in
                                                (match uu___22 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu___23 -> tm1)
                                            | uu___20 -> tm1)
                                       | uu___17 -> tm1
                                     else
                                       (let uu___18 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid in
                                        if uu___18
                                        then
                                          match args with
                                          | (t, uu___19)::[] ->
                                              let uu___20 =
                                                let uu___21 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu___21.FStar_Syntax_Syntax.n in
                                              (match uu___20 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu___21::[], body,
                                                    uu___22)
                                                   ->
                                                   let uu___23 = simp_t body in
                                                   (match uu___23 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu___24 -> tm1)
                                               | uu___21 -> tm1)
                                          | (ty, FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu___19))::(t, uu___20)::[] ->
                                              let uu___21 =
                                                let uu___22 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu___22.FStar_Syntax_Syntax.n in
                                              (match uu___21 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu___22::[], body,
                                                    uu___23)
                                                   ->
                                                   let uu___24 = simp_t body in
                                                   (match uu___24 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | FStar_Pervasives_Native.Some
                                                        (true) when
                                                        clearly_inhabited ty
                                                        ->
                                                        w
                                                          FStar_Syntax_Util.t_true
                                                    | uu___25 -> tm1)
                                               | uu___22 -> tm1)
                                          | uu___19 -> tm1
                                        else
                                          (let uu___20 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid in
                                           if uu___20
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu___21;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu___22;_},
                                                uu___23)::[] ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu___21;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu___22;_},
                                                uu___23)::[] ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu___21 -> tm1
                                           else
                                             (let uu___22 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid in
                                              if uu___22
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid] in
                                                  let uu___23 =
                                                    let uu___24 =
                                                      FStar_Syntax_Subst.compress
                                                        t in
                                                    uu___24.FStar_Syntax_Syntax.n in
                                                  match uu___23 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu___24 -> false in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu___23 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd in
                                                     FStar_All.pipe_right
                                                       uu___23
                                                       FStar_Pervasives_Native.fst in
                                                   let uu___23 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure in
                                                   (if uu___23
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu___25 =
                                                         let uu___26 =
                                                           FStar_Syntax_Subst.compress
                                                             t in
                                                         uu___26.FStar_Syntax_Syntax.n in
                                                       match uu___25 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu___26 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t in
                                                           let uu___27 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure in
                                                           if uu___27
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu___29 =
                                                                  let uu___30
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1 in
                                                                  uu___30.FStar_Syntax_Syntax.n in
                                                                match uu___29
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd,
                                                                    uu___30)
                                                                    -> hd
                                                                | uu___30 ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app" in
                                                              let uu___29 =
                                                                let uu___30 =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg in
                                                                [uu___30] in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu___29)
                                                       | uu___26 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu___24 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1 in
                                                 match uu___24 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero,
                                                      t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu___25 ->
                                                     let uu___26 =
                                                       norm_cb cfg in
                                                     reduce_equality uu___26
                                                       cfg env1 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv, t) ->
                      let uu___4 = simp_t t in
                      (match uu___4 with
                       | FStar_Pervasives_Native.Some (true) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false) -> tm1
                       | FStar_Pervasives_Native.None -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu___4 ->
                      let uu___5 = is_const_match tm1 in
                      (match uu___5 with
                       | FStar_Pervasives_Native.Some (true) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None -> tm1)
                  | uu___4 -> tm1))
and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun t ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu___1 ->
               (let uu___3 = FStar_Syntax_Print.tag_of_term t in
                let uu___4 = FStar_Syntax_Print.term_to_string t in
                let uu___5 =
                  FStar_Util.string_of_int (FStar_List.length env1) in
                let uu___6 =
                  let uu___7 =
                    let uu___8 = firstn (Prims.of_int (4)) stack1 in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst uu___8 in
                  stack_to_string uu___7 in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu___3 uu___4 uu___5 uu___6);
               (let uu___3 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild") in
                if uu___3
                then
                  let uu___4 = FStar_Syntax_Util.unbound_variables t in
                  match uu___4 with
                  | [] -> ()
                  | bvs ->
                      ((let uu___6 = FStar_Syntax_Print.tag_of_term t in
                        let uu___7 = FStar_Syntax_Print.term_to_string t in
                        let uu___8 =
                          let uu___9 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string) in
                          FStar_All.pipe_right uu___9
                            (FStar_String.concat ", ") in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu___6 uu___7
                          uu___8);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t in
           let uu___1 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack1 with
                | (Arg uu___2)::uu___3 -> true
                | uu___2 -> false) in
           if uu___1
           then
             let uu___2 = FStar_All.pipe_right f_opt FStar_Util.must in
             FStar_All.pipe_right uu___2 (norm cfg env1 stack1)
           else
             (let t1 = maybe_simplify cfg env1 stack1 t in
              match stack1 with
              | [] -> t1
              | (Cfg (cfg1, dbg))::stack2 ->
                  (maybe_debug cfg1 t1 dbg; rebuild cfg1 env1 stack2 t1)
              | (Meta (uu___3, m, r))::stack2 ->
                  let t2 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_meta (t1, m)) r in
                  rebuild cfg env1 stack2 t2
              | (MemoLazy r)::stack2 ->
                  (set_memo cfg r (env1, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu___5 ->
                        let uu___6 = FStar_Syntax_Print.term_to_string t1 in
                        FStar_Util.print1 "\tSet memo %s\n" uu___6);
                   rebuild cfg env1 stack2 t1)
              | (Let (env', bs, lb, r))::stack2 ->
                  let body = FStar_Syntax_Subst.close bs t1 in
                  let t2 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body)) r in
                  rebuild cfg env' stack2 t2
              | (Abs (env', bs, env'', lopt, r))::stack2 ->
                  let bs1 = norm_binders cfg env' bs in
                  let lopt1 = norm_lcomp_opt cfg env'' lopt in
                  let uu___3 =
                    let uu___4 = FStar_Syntax_Util.abs bs1 t1 lopt1 in
                    {
                      FStar_Syntax_Syntax.n = (uu___4.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___4.FStar_Syntax_Syntax.vars)
                    } in
                  rebuild cfg env1 stack2 uu___3
              | (Arg (Univ uu___3, uu___4, uu___5))::uu___6 ->
                  failwith "Impossible"
              | (Arg (Dummy, uu___3, uu___4))::uu___5 ->
                  failwith "Impossible"
              | (UnivArgs (us, r))::stack2 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us in
                  rebuild cfg env1 stack2 t2
              | (Arg (Clos (env_arg, tm, uu___3, uu___4), aq, r))::stack2
                  when
                  let uu___5 = head_of t1 in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu___5 ->
                  let t2 =
                    let uu___5 =
                      let uu___6 = closure_as_term cfg env_arg tm in
                      (uu___6, aq) in
                    FStar_Syntax_Syntax.extend_app t1 uu___5 r in
                  rebuild cfg env1 stack2 t2
              | (Arg (Clos (env_arg, tm, m, uu___3), aq, r))::stack2 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu___5 ->
                        let uu___6 = FStar_Syntax_Print.term_to_string tm in
                        FStar_Util.print1 "Rebuilding with arg %s\n" uu___6);
                   if
                     Prims.op_Negation
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                   then
                     (let uu___5 =
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
                          &&
                          (let uu___6 = is_partial_primop_app cfg t1 in
                           Prims.op_Negation uu___6) in
                      if uu___5
                      then
                        let arg = closure_as_term cfg env_arg tm in
                        let t2 =
                          FStar_Syntax_Syntax.extend_app t1 (arg, aq) r in
                        rebuild cfg env_arg stack2 t2
                      else
                        (let stack3 = (App (env1, t1, aq, r)) :: stack2 in
                         norm cfg env_arg stack3 tm))
                   else
                     (let uu___6 = FStar_ST.op_Bang m in
                      match uu___6 with
                      | FStar_Pervasives_Native.None ->
                          let uu___7 =
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
                              &&
                              (let uu___8 = is_partial_primop_app cfg t1 in
                               Prims.op_Negation uu___8) in
                          if uu___7
                          then
                            let arg = closure_as_term cfg env_arg tm in
                            let t2 =
                              FStar_Syntax_Syntax.extend_app t1 (arg, aq) r in
                            rebuild cfg env_arg stack2 t2
                          else
                            (let stack3 = (MemoLazy m) ::
                               (App (env1, t1, aq, r)) :: stack2 in
                             norm cfg env_arg stack3 tm)
                      | FStar_Pervasives_Native.Some (uu___7, a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq) r in
                          rebuild cfg env_arg stack2 t2))
              | (App (env2, head, aq, r))::stack' when
                  should_reify cfg stack1 ->
                  let t0 = t1 in
                  let fallback msg uu___3 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu___5 ->
                         let uu___6 = FStar_Syntax_Print.term_to_string t1 in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg uu___6);
                    (let t2 = FStar_Syntax_Syntax.extend_app head (t1, aq) r in
                     rebuild cfg env2 stack' t2) in
                  let is_layered_effect m =
                    let uu___3 =
                      FStar_All.pipe_right m
                        (FStar_TypeChecker_Env.norm_eff_name
                           cfg.FStar_TypeChecker_Cfg.tcenv) in
                    FStar_All.pipe_right uu___3
                      (FStar_TypeChecker_Env.is_layered_effect
                         cfg.FStar_TypeChecker_Cfg.tcenv) in
                  let uu___3 =
                    let uu___4 = FStar_Syntax_Subst.compress t1 in
                    uu___4.FStar_Syntax_Syntax.n in
                  (match uu___3 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (uu___4, FStar_Syntax_Syntax.Meta_monadic (m, uu___5))
                       when
                       (FStar_All.pipe_right m is_layered_effect) &&
                         (Prims.op_Negation
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction)
                       ->
                       let uu___6 =
                         let uu___7 = FStar_Ident.string_of_lid m in
                         FStar_Util.format1
                           "Meta_monadic for a layered effect %s in non-extraction mode"
                           uu___7 in
                       fallback uu___6 ()
                   | FStar_Syntax_Syntax.Tm_meta
                       (uu___4, FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc, mtgt, uu___5))
                       when
                       ((is_layered_effect msrc) || (is_layered_effect mtgt))
                         &&
                         (Prims.op_Negation
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction)
                       ->
                       let uu___6 =
                         let uu___7 = FStar_Ident.string_of_lid msrc in
                         let uu___8 = FStar_Ident.string_of_lid mtgt in
                         FStar_Util.format2
                           "Meta_monadic_lift for layered effect %s ~> %s in non extraction mode"
                           uu___7 uu___8 in
                       fallback uu___6 ()
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2, FStar_Syntax_Syntax.Meta_monadic (m, ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env2 stack1 t2
                         m ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2, FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc, mtgt, ty))
                       ->
                       let lifted =
                         let uu___4 = closure_as_term cfg env2 ty in
                         reify_lift cfg t2 msrc mtgt uu___4 in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu___5 ->
                             let uu___6 =
                               FStar_Syntax_Print.term_to_string lifted in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu___6);
                        (let uu___5 = FStar_List.tl stack1 in
                         norm cfg env2 uu___5 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu___4);
                          FStar_Syntax_Syntax.pos = uu___5;
                          FStar_Syntax_Syntax.vars = uu___6;_},
                        (e, uu___7)::[])
                       -> norm cfg env2 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu___4 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu___5 = FStar_Syntax_Util.head_and_args t1 in
                       (match uu___5 with
                        | (hd, args) ->
                            let uu___6 =
                              let uu___7 = FStar_Syntax_Util.un_uinst hd in
                              uu___7.FStar_Syntax_Syntax.n in
                            (match uu___6 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu___7 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv in
                                 (match uu___7 with
                                  | FStar_Pervasives_Native.Some
                                      { FStar_TypeChecker_Cfg.name = uu___8;
                                        FStar_TypeChecker_Cfg.arity = uu___9;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu___10;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu___11;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu___12;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu___13;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu___14;_}
                                      when (FStar_List.length args) = n ->
                                      norm cfg env2 stack' t1
                                  | uu___8 -> fallback " (3)" ())
                             | uu___7 -> fallback " (4)" ()))
                   | uu___4 -> fallback " (2)" ())
              | (App (env2, head, aq, r))::stack2 ->
                  let t2 = FStar_Syntax_Syntax.extend_app head (t1, aq) r in
                  rebuild cfg env2 stack2 t2
              | (CBVApp (env', head, aq, r))::stack2 ->
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None in
                            (env1, t1, uu___8, false) in
                          Clos uu___7 in
                        (uu___6, aq, (t1.FStar_Syntax_Syntax.pos)) in
                      Arg uu___5 in
                    uu___4 :: stack2 in
                  norm cfg env' uu___3 head
              | (Match (env', asc_opt, branches1, cfg1, r))::stack2 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu___4 ->
                        let uu___5 = FStar_Syntax_Print.term_to_string t1 in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu___5);
                   (let scrutinee_env = env1 in
                    let env2 = env' in
                    let scrutinee = t1 in
                    let norm_and_rebuild_match uu___4 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu___6 ->
                           let uu___7 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           let uu___8 =
                             let uu___9 =
                               FStar_All.pipe_right branches1
                                 (FStar_List.map
                                    (fun uu___10 ->
                                       match uu___10 with
                                       | (p, uu___11, uu___12) ->
                                           FStar_Syntax_Print.pat_to_string p)) in
                             FStar_All.pipe_right uu___9
                               (FStar_String.concat "\n\t") in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu___7 uu___8);
                      (let whnf =
                         (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                           ||
                           (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf in
                       let cfg_exclude_zeta =
                         if
                           (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full
                         then cfg1
                         else
                           (let new_delta =
                              FStar_All.pipe_right
                                cfg1.FStar_TypeChecker_Cfg.delta_level
                                (FStar_List.filter
                                   (fun uu___7 ->
                                      match uu___7 with
                                      | FStar_TypeChecker_Env.InliningDelta
                                          -> true
                                      | FStar_TypeChecker_Env.Eager_unfolding_only
                                          -> true
                                      | uu___8 -> false)) in
                            let steps =
                              let uu___7 = cfg1.FStar_TypeChecker_Cfg.steps in
                              {
                                FStar_TypeChecker_Cfg.beta =
                                  (uu___7.FStar_TypeChecker_Cfg.beta);
                                FStar_TypeChecker_Cfg.iota =
                                  (uu___7.FStar_TypeChecker_Cfg.iota);
                                FStar_TypeChecker_Cfg.zeta = false;
                                FStar_TypeChecker_Cfg.zeta_full =
                                  (uu___7.FStar_TypeChecker_Cfg.zeta_full);
                                FStar_TypeChecker_Cfg.weak =
                                  (uu___7.FStar_TypeChecker_Cfg.weak);
                                FStar_TypeChecker_Cfg.hnf =
                                  (uu___7.FStar_TypeChecker_Cfg.hnf);
                                FStar_TypeChecker_Cfg.primops =
                                  (uu___7.FStar_TypeChecker_Cfg.primops);
                                FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                  =
                                  (uu___7.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                FStar_TypeChecker_Cfg.unfold_until =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_only =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_fully =
                                  (uu___7.FStar_TypeChecker_Cfg.unfold_fully);
                                FStar_TypeChecker_Cfg.unfold_attr =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_qual =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_tac = false;
                                FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                  =
                                  (uu___7.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                FStar_TypeChecker_Cfg.simplify =
                                  (uu___7.FStar_TypeChecker_Cfg.simplify);
                                FStar_TypeChecker_Cfg.erase_universes =
                                  (uu___7.FStar_TypeChecker_Cfg.erase_universes);
                                FStar_TypeChecker_Cfg.allow_unbound_universes
                                  =
                                  (uu___7.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                FStar_TypeChecker_Cfg.reify_ =
                                  (uu___7.FStar_TypeChecker_Cfg.reify_);
                                FStar_TypeChecker_Cfg.compress_uvars =
                                  (uu___7.FStar_TypeChecker_Cfg.compress_uvars);
                                FStar_TypeChecker_Cfg.no_full_norm =
                                  (uu___7.FStar_TypeChecker_Cfg.no_full_norm);
                                FStar_TypeChecker_Cfg.check_no_uvars =
                                  (uu___7.FStar_TypeChecker_Cfg.check_no_uvars);
                                FStar_TypeChecker_Cfg.unmeta =
                                  (uu___7.FStar_TypeChecker_Cfg.unmeta);
                                FStar_TypeChecker_Cfg.unascribe =
                                  (uu___7.FStar_TypeChecker_Cfg.unascribe);
                                FStar_TypeChecker_Cfg.in_full_norm_request =
                                  (uu___7.FStar_TypeChecker_Cfg.in_full_norm_request);
                                FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                  =
                                  (uu___7.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                                FStar_TypeChecker_Cfg.nbe_step =
                                  (uu___7.FStar_TypeChecker_Cfg.nbe_step);
                                FStar_TypeChecker_Cfg.for_extraction =
                                  (uu___7.FStar_TypeChecker_Cfg.for_extraction)
                              } in
                            let uu___7 = cfg1 in
                            {
                              FStar_TypeChecker_Cfg.steps = steps;
                              FStar_TypeChecker_Cfg.tcenv =
                                (uu___7.FStar_TypeChecker_Cfg.tcenv);
                              FStar_TypeChecker_Cfg.debug =
                                (uu___7.FStar_TypeChecker_Cfg.debug);
                              FStar_TypeChecker_Cfg.delta_level = new_delta;
                              FStar_TypeChecker_Cfg.primitive_steps =
                                (uu___7.FStar_TypeChecker_Cfg.primitive_steps);
                              FStar_TypeChecker_Cfg.strong = true;
                              FStar_TypeChecker_Cfg.memoize_lazy =
                                (uu___7.FStar_TypeChecker_Cfg.memoize_lazy);
                              FStar_TypeChecker_Cfg.normalize_pure_lets =
                                (uu___7.FStar_TypeChecker_Cfg.normalize_pure_lets);
                              FStar_TypeChecker_Cfg.reifying =
                                (uu___7.FStar_TypeChecker_Cfg.reifying)
                            }) in
                       let norm_or_whnf env3 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env3 t2
                         else norm cfg_exclude_zeta env3 [] t2 in
                       let norm_ascription uu___6 =
                         match uu___6 with
                         | (tc, tacopt) ->
                             let tc1 =
                               match tc with
                               | FStar_Pervasives.Inl t2 ->
                                   let uu___7 = norm cfg1 env2 [] t2 in
                                   FStar_Pervasives.Inl uu___7
                               | FStar_Pervasives.Inr c ->
                                   let uu___7 = norm_comp cfg1 env2 c in
                                   FStar_Pervasives.Inr uu___7 in
                             let tacopt1 =
                               FStar_Util.map_opt tacopt (norm cfg1 env2 []) in
                             (tc1, tacopt1) in
                       let rec norm_pat env3 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu___6 ->
                             (p, env3)
                         | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
                             let uu___6 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu___7 ->
                                       fun uu___8 ->
                                         match (uu___7, uu___8) with
                                         | ((pats1, env4), (p1, b)) ->
                                             let uu___9 = norm_pat env4 p1 in
                                             (match uu___9 with
                                              | (p2, env5) ->
                                                  (((p2, b) :: pats1), env5)))
                                    ([], env3)) in
                             (match uu___6 with
                              | (pats1, env4) ->
                                  ((let uu___7 = p in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___7.FStar_Syntax_Syntax.p)
                                    }), env4))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___6 = x in
                               let uu___7 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___6.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___6.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu___7
                               } in
                             ((let uu___6 = p in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___6.FStar_Syntax_Syntax.p)
                               }), (dummy :: env3))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___6 = x in
                               let uu___7 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___6.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___6.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu___7
                               } in
                             ((let uu___6 = p in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___6.FStar_Syntax_Syntax.p)
                               }), (dummy :: env3))
                         | FStar_Syntax_Syntax.Pat_dot_term (x, t2) ->
                             let x1 =
                               let uu___6 = x in
                               let uu___7 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___6.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___6.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu___7
                               } in
                             let t3 = norm_or_whnf env3 t2 in
                             ((let uu___6 = p in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___6.FStar_Syntax_Syntax.p)
                               }), env3) in
                       let norm_branches uu___6 =
                         match env2 with
                         | [] when whnf -> branches1
                         | uu___7 ->
                             FStar_All.pipe_right branches1
                               (FStar_List.map
                                  (fun branch ->
                                     let uu___8 =
                                       FStar_Syntax_Subst.open_branch branch in
                                     match uu___8 with
                                     | (p, wopt, e) ->
                                         let uu___9 = norm_pat env2 p in
                                         (match uu___9 with
                                          | (p1, env3) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                    ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu___10 =
                                                      norm_or_whnf env3 w in
                                                    FStar_Pervasives_Native.Some
                                                      uu___10 in
                                              let e1 = norm_or_whnf env3 e in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1)))) in
                       let maybe_commute_matches uu___6 =
                         let can_commute =
                           match branches1 with
                           | ({
                                FStar_Syntax_Syntax.v =
                                  FStar_Syntax_Syntax.Pat_cons (fv, uu___7);
                                FStar_Syntax_Syntax.p = uu___8;_},
                              uu___9, uu___10)::uu___11 ->
                               FStar_TypeChecker_Env.fv_has_attr
                                 cfg1.FStar_TypeChecker_Cfg.tcenv fv
                                 FStar_Parser_Const.commute_nested_matches_lid
                           | uu___7 -> false in
                         let uu___7 =
                           let uu___8 = FStar_Syntax_Util.unascribe scrutinee in
                           uu___8.FStar_Syntax_Syntax.n in
                         match uu___7 with
                         | FStar_Syntax_Syntax.Tm_match
                             (sc0, asc_opt0, branches0) when can_commute ->
                             let reduce_branch b =
                               let stack3 =
                                 [Match (env', asc_opt, branches1, cfg1, r)] in
                               let uu___8 = FStar_Syntax_Subst.open_branch b in
                               match uu___8 with
                               | (p, wopt, e) ->
                                   let uu___9 = norm_pat scrutinee_env p in
                                   (match uu___9 with
                                    | (p1, branch_env) ->
                                        let wopt1 =
                                          match wopt with
                                          | FStar_Pervasives_Native.None ->
                                              FStar_Pervasives_Native.None
                                          | FStar_Pervasives_Native.Some w ->
                                              let uu___10 =
                                                norm_or_whnf branch_env w in
                                              FStar_Pervasives_Native.Some
                                                uu___10 in
                                        let e1 =
                                          norm cfg1 branch_env stack3 e in
                                        FStar_Syntax_Util.branch
                                          (p1, wopt1, e1)) in
                             let branches01 =
                               FStar_List.map reduce_branch branches0 in
                             let uu___8 =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_match
                                    (sc0, asc_opt0, branches01)) r in
                             rebuild cfg1 env2 stack2 uu___8
                         | uu___8 ->
                             let scrutinee1 =
                               let uu___9 =
                                 ((((cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                                      &&
                                      (Prims.op_Negation
                                         (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak))
                                     &&
                                     (Prims.op_Negation
                                        (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars))
                                    &&
                                    (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weakly_reduce_scrutinee)
                                   && (maybe_weakly_reduced scrutinee) in
                               if uu___9
                               then
                                 norm
                                   (let uu___10 = cfg1 in
                                    {
                                      FStar_TypeChecker_Cfg.steps =
                                        (let uu___11 =
                                           cfg1.FStar_TypeChecker_Cfg.steps in
                                         {
                                           FStar_TypeChecker_Cfg.beta =
                                             (uu___11.FStar_TypeChecker_Cfg.beta);
                                           FStar_TypeChecker_Cfg.iota =
                                             (uu___11.FStar_TypeChecker_Cfg.iota);
                                           FStar_TypeChecker_Cfg.zeta =
                                             (uu___11.FStar_TypeChecker_Cfg.zeta);
                                           FStar_TypeChecker_Cfg.zeta_full =
                                             (uu___11.FStar_TypeChecker_Cfg.zeta_full);
                                           FStar_TypeChecker_Cfg.weak =
                                             (uu___11.FStar_TypeChecker_Cfg.weak);
                                           FStar_TypeChecker_Cfg.hnf =
                                             (uu___11.FStar_TypeChecker_Cfg.hnf);
                                           FStar_TypeChecker_Cfg.primops =
                                             (uu___11.FStar_TypeChecker_Cfg.primops);
                                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                             =
                                             (uu___11.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                           FStar_TypeChecker_Cfg.unfold_until
                                             =
                                             (uu___11.FStar_TypeChecker_Cfg.unfold_until);
                                           FStar_TypeChecker_Cfg.unfold_only
                                             =
                                             (uu___11.FStar_TypeChecker_Cfg.unfold_only);
                                           FStar_TypeChecker_Cfg.unfold_fully
                                             =
                                             (uu___11.FStar_TypeChecker_Cfg.unfold_fully);
                                           FStar_TypeChecker_Cfg.unfold_attr
                                             =
                                             (uu___11.FStar_TypeChecker_Cfg.unfold_attr);
                                           FStar_TypeChecker_Cfg.unfold_qual
                                             =
                                             (uu___11.FStar_TypeChecker_Cfg.unfold_qual);
                                           FStar_TypeChecker_Cfg.unfold_tac =
                                             (uu___11.FStar_TypeChecker_Cfg.unfold_tac);
                                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                             =
                                             (uu___11.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                           FStar_TypeChecker_Cfg.simplify =
                                             (uu___11.FStar_TypeChecker_Cfg.simplify);
                                           FStar_TypeChecker_Cfg.erase_universes
                                             =
                                             (uu___11.FStar_TypeChecker_Cfg.erase_universes);
                                           FStar_TypeChecker_Cfg.allow_unbound_universes
                                             =
                                             (uu___11.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                           FStar_TypeChecker_Cfg.reify_ =
                                             (uu___11.FStar_TypeChecker_Cfg.reify_);
                                           FStar_TypeChecker_Cfg.compress_uvars
                                             =
                                             (uu___11.FStar_TypeChecker_Cfg.compress_uvars);
                                           FStar_TypeChecker_Cfg.no_full_norm
                                             =
                                             (uu___11.FStar_TypeChecker_Cfg.no_full_norm);
                                           FStar_TypeChecker_Cfg.check_no_uvars
                                             =
                                             (uu___11.FStar_TypeChecker_Cfg.check_no_uvars);
                                           FStar_TypeChecker_Cfg.unmeta =
                                             (uu___11.FStar_TypeChecker_Cfg.unmeta);
                                           FStar_TypeChecker_Cfg.unascribe =
                                             (uu___11.FStar_TypeChecker_Cfg.unascribe);
                                           FStar_TypeChecker_Cfg.in_full_norm_request
                                             =
                                             (uu___11.FStar_TypeChecker_Cfg.in_full_norm_request);
                                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                             = false;
                                           FStar_TypeChecker_Cfg.nbe_step =
                                             (uu___11.FStar_TypeChecker_Cfg.nbe_step);
                                           FStar_TypeChecker_Cfg.for_extraction
                                             =
                                             (uu___11.FStar_TypeChecker_Cfg.for_extraction)
                                         });
                                      FStar_TypeChecker_Cfg.tcenv =
                                        (uu___10.FStar_TypeChecker_Cfg.tcenv);
                                      FStar_TypeChecker_Cfg.debug =
                                        (uu___10.FStar_TypeChecker_Cfg.debug);
                                      FStar_TypeChecker_Cfg.delta_level =
                                        (uu___10.FStar_TypeChecker_Cfg.delta_level);
                                      FStar_TypeChecker_Cfg.primitive_steps =
                                        (uu___10.FStar_TypeChecker_Cfg.primitive_steps);
                                      FStar_TypeChecker_Cfg.strong =
                                        (uu___10.FStar_TypeChecker_Cfg.strong);
                                      FStar_TypeChecker_Cfg.memoize_lazy =
                                        (uu___10.FStar_TypeChecker_Cfg.memoize_lazy);
                                      FStar_TypeChecker_Cfg.normalize_pure_lets
                                        =
                                        (uu___10.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                      FStar_TypeChecker_Cfg.reifying =
                                        (uu___10.FStar_TypeChecker_Cfg.reifying)
                                    }) scrutinee_env [] scrutinee
                               else scrutinee in
                             let asc_opt1 =
                               FStar_Util.map_opt asc_opt norm_ascription in
                             let branches2 = norm_branches () in
                             let uu___9 =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_match
                                    (scrutinee1, asc_opt1, branches2)) r in
                             rebuild cfg1 env2 stack2 uu___9 in
                       maybe_commute_matches ()) in
                    let rec is_cons head =
                      let uu___4 =
                        let uu___5 = FStar_Syntax_Subst.compress head in
                        uu___5.FStar_Syntax_Syntax.n in
                      match uu___4 with
                      | FStar_Syntax_Syntax.Tm_uinst (h, uu___5) -> is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu___5 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu___5;
                            FStar_Syntax_Syntax.fv_delta = uu___6;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor);_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu___5;
                            FStar_Syntax_Syntax.fv_delta = uu___6;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu___7);_}
                          -> true
                      | uu___5 -> false in
                    let guard_when_clause wopt b rest =
                      match wopt with
                      | FStar_Pervasives_Native.None -> b
                      | FStar_Pervasives_Native.Some w ->
                          let then_branch = b in
                          let else_branch =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_match
                                 (scrutinee, asc_opt, rest)) r in
                          FStar_Syntax_Util.if_then_else w then_branch
                            else_branch in
                    let rec matches_pat scrutinee_orig p =
                      let scrutinee1 =
                        FStar_Syntax_Util.unmeta scrutinee_orig in
                      let scrutinee2 = FStar_Syntax_Util.unlazy scrutinee1 in
                      let uu___4 = FStar_Syntax_Util.head_and_args scrutinee2 in
                      match uu___4 with
                      | (head, args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Pervasives.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Pervasives.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu___5 ->
                               FStar_Pervasives.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Pervasives.Inl []
                                | uu___5 ->
                                    let uu___6 =
                                      let uu___7 = is_cons head in
                                      Prims.op_Negation uu___7 in
                                    FStar_Pervasives.Inr uu___6)
                           | FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) ->
                               let uu___5 =
                                 let uu___6 = FStar_Syntax_Util.un_uinst head in
                                 uu___6.FStar_Syntax_Syntax.n in
                               (match uu___5 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu___6 ->
                                    let uu___7 =
                                      let uu___8 = is_cons head in
                                      Prims.op_Negation uu___8 in
                                    FStar_Pervasives.Inr uu___7))
                    and matches_args out a p =
                      match (a, p) with
                      | ([], []) -> FStar_Pervasives.Inl out
                      | ((t2, uu___4)::rest_a, (p1, uu___5)::rest_p) ->
                          let uu___6 = matches_pat t2 p1 in
                          (match uu___6 with
                           | FStar_Pervasives.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu___4 -> FStar_Pervasives.Inr false in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1, wopt, b)::rest ->
                          let uu___4 = matches_pat scrutinee1 p1 in
                          (match uu___4 with
                           | FStar_Pervasives.Inr (false) ->
                               matches scrutinee1 rest
                           | FStar_Pervasives.Inr (true) ->
                               norm_and_rebuild_match ()
                           | FStar_Pervasives.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu___6 ->
                                     let uu___7 =
                                       FStar_Syntax_Print.pat_to_string p1 in
                                     let uu___8 =
                                       let uu___9 =
                                         FStar_List.map
                                           (fun uu___10 ->
                                              match uu___10 with
                                              | (uu___11, t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s in
                                       FStar_All.pipe_right uu___9
                                         (FStar_String.concat "; ") in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu___7 uu___8);
                                (let env0 = env2 in
                                 let env3 =
                                   FStar_List.fold_left
                                     (fun env4 ->
                                        fun uu___6 ->
                                          match uu___6 with
                                          | (bv, t2) ->
                                              let uu___7 =
                                                let uu___8 =
                                                  let uu___9 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv in
                                                  FStar_Pervasives_Native.Some
                                                    uu___9 in
                                                let uu___9 =
                                                  let uu___10 =
                                                    let uu___11 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2)) in
                                                    ([], t2, uu___11, false) in
                                                  Clos uu___10 in
                                                (uu___8, uu___9) in
                                              uu___7 :: env4) env2 s in
                                 let uu___6 = guard_when_clause wopt b rest in
                                 norm cfg1 env3 stack2 uu___6))) in
                    if
                      (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                    then matches scrutinee branches1
                    else norm_and_rebuild_match ()))))
let (reflection_env_hook :
  FStar_TypeChecker_Env.env FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let (normalize_with_primitive_steps :
  FStar_TypeChecker_Cfg.primitive_step Prims.list ->
    FStar_TypeChecker_Env.steps ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun ps ->
    fun s ->
      fun e ->
        fun t ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_TypeChecker_Env.current_module e in
              FStar_Ident.string_of_lid uu___2 in
            FStar_Pervasives_Native.Some uu___1 in
          FStar_Profiling.profile
            (fun uu___1 ->
               let c = FStar_TypeChecker_Cfg.config' ps s e in
               FStar_ST.op_Colon_Equals reflection_env_hook
                 (FStar_Pervasives_Native.Some e);
               FStar_ST.op_Colon_Equals plugin_unfold_warn_ctr
                 (Prims.of_int (10));
               FStar_TypeChecker_Cfg.log_cfg c
                 (fun uu___5 ->
                    let uu___6 = FStar_TypeChecker_Cfg.cfg_to_string c in
                    FStar_Util.print1 "Cfg = %s\n" uu___6);
               (let uu___5 = is_nbe_request s in
                if uu___5
                then
                  (FStar_TypeChecker_Cfg.log_top c
                     (fun uu___7 ->
                        let uu___8 = FStar_Syntax_Print.term_to_string t in
                        FStar_Util.print1 "Starting NBE for (%s) {\n" uu___8);
                   FStar_TypeChecker_Cfg.log_top c
                     (fun uu___8 ->
                        let uu___9 = FStar_TypeChecker_Cfg.cfg_to_string c in
                        FStar_Util.print1 ">>> cfg = %s\n" uu___9);
                   (let uu___8 =
                      FStar_Errors.with_ctx
                        "While normalizing a term via NBE"
                        (fun uu___9 ->
                           FStar_Util.record_time
                             (fun uu___10 -> nbe_eval c s t)) in
                    match uu___8 with
                    | (r, ms) ->
                        (FStar_TypeChecker_Cfg.log_top c
                           (fun uu___10 ->
                              let uu___11 =
                                FStar_Syntax_Print.term_to_string r in
                              let uu___12 = FStar_Util.string_of_int ms in
                              FStar_Util.print2
                                "}\nNormalization result = (%s) in %s ms\n"
                                uu___11 uu___12);
                         r)))
                else
                  (FStar_TypeChecker_Cfg.log_top c
                     (fun uu___8 ->
                        let uu___9 = FStar_Syntax_Print.term_to_string t in
                        FStar_Util.print1 "Starting normalizer for (%s) {\n"
                          uu___9);
                   FStar_TypeChecker_Cfg.log_top c
                     (fun uu___9 ->
                        let uu___10 = FStar_TypeChecker_Cfg.cfg_to_string c in
                        FStar_Util.print1 ">>> cfg = %s\n" uu___10);
                   (let uu___9 =
                      FStar_Errors.with_ctx "While normalizing a term"
                        (fun uu___10 ->
                           FStar_Util.record_time
                             (fun uu___11 -> norm c [] [] t)) in
                    match uu___9 with
                    | (r, ms) ->
                        (FStar_TypeChecker_Cfg.log_top c
                           (fun uu___11 ->
                              let uu___12 =
                                FStar_Syntax_Print.term_to_string r in
                              let uu___13 = FStar_Util.string_of_int ms in
                              FStar_Util.print2
                                "}\nNormalization result = (%s) in %s ms\n"
                                uu___12 uu___13);
                         r))))) uu___
            "FStar.TypeChecker.Normalize.normalize_with_primitive_steps"
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s ->
    fun e ->
      fun t ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_TypeChecker_Env.current_module e in
            FStar_Ident.string_of_lid uu___2 in
          FStar_Pervasives_Native.Some uu___1 in
        FStar_Profiling.profile
          (fun uu___1 -> normalize_with_primitive_steps [] s e t) uu___
          "FStar.TypeChecker.Normalize.normalize"
let (normalize_comp :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun s ->
    fun e ->
      fun c ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_TypeChecker_Env.current_module e in
            FStar_Ident.string_of_lid uu___2 in
          FStar_Pervasives_Native.Some uu___1 in
        FStar_Profiling.profile
          (fun uu___1 ->
             let cfg = FStar_TypeChecker_Cfg.config s e in
             FStar_ST.op_Colon_Equals reflection_env_hook
               (FStar_Pervasives_Native.Some e);
             FStar_ST.op_Colon_Equals plugin_unfold_warn_ctr
               (Prims.of_int (10));
             FStar_TypeChecker_Cfg.log_top cfg
               (fun uu___5 ->
                  let uu___6 = FStar_Syntax_Print.comp_to_string c in
                  FStar_Util.print1
                    "Starting normalizer for computation (%s) {\n" uu___6);
             FStar_TypeChecker_Cfg.log_top cfg
               (fun uu___6 ->
                  let uu___7 = FStar_TypeChecker_Cfg.cfg_to_string cfg in
                  FStar_Util.print1 ">>> cfg = %s\n" uu___7);
             (let uu___6 =
                FStar_Errors.with_ctx "While normalizing a computation type"
                  (fun uu___7 ->
                     FStar_Util.record_time
                       (fun uu___8 -> norm_comp cfg [] c)) in
              match uu___6 with
              | (c1, ms) ->
                  (FStar_TypeChecker_Cfg.log_top cfg
                     (fun uu___8 ->
                        let uu___9 = FStar_Syntax_Print.comp_to_string c1 in
                        let uu___10 = FStar_Util.string_of_int ms in
                        FStar_Util.print2
                          "}\nNormalization result = (%s) in %s ms\n" uu___9
                          uu___10);
                   c1))) uu___ "FStar.TypeChecker.Normalize.normalize_comp"
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env1 ->
    fun u ->
      let uu___ = FStar_TypeChecker_Cfg.config [] env1 in
      norm_universe uu___ [] u
let (non_info_norm :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env1 ->
    fun t ->
      let steps =
        [FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.AllowUnboundUniverses;
        FStar_TypeChecker_Env.EraseUniverses;
        FStar_TypeChecker_Env.HNF;
        FStar_TypeChecker_Env.Unascribe;
        FStar_TypeChecker_Env.ForExtraction] in
      let uu___ = normalize steps env1 t in
      FStar_TypeChecker_Env.non_informative env1 uu___
let (maybe_promote_t :
  FStar_TypeChecker_Env.env ->
    Prims.bool -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun env1 ->
    fun non_informative_only ->
      fun t ->
        (Prims.op_Negation non_informative_only) || (non_info_norm env1 t)
let (ghost_to_pure_aux :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun env1 ->
    fun non_informative_only ->
      fun c ->
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu___ -> c
        | FStar_Syntax_Syntax.GTotal (t, uopt) ->
            let uu___ = maybe_promote_t env1 non_informative_only t in
            if uu___
            then
              let uu___1 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
                FStar_Syntax_Syntax.pos = (uu___1.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars = (uu___1.FStar_Syntax_Syntax.vars)
              }
            else c
        | FStar_Syntax_Syntax.Comp ct ->
            let l =
              FStar_TypeChecker_Env.norm_eff_name env1
                ct.FStar_Syntax_Syntax.effect_name in
            let uu___ =
              (FStar_Syntax_Util.is_ghost_effect l) &&
                (maybe_promote_t env1 non_informative_only
                   ct.FStar_Syntax_Syntax.result_typ) in
            if uu___
            then
              let ct1 =
                let uu___1 =
                  downgrade_ghost_effect_name
                    ct.FStar_Syntax_Syntax.effect_name in
                match uu___1 with
                | FStar_Pervasives_Native.Some pure_eff ->
                    let flags =
                      let uu___2 =
                        FStar_Ident.lid_equals pure_eff
                          FStar_Parser_Const.effect_Tot_lid in
                      if uu___2
                      then FStar_Syntax_Syntax.TOTAL ::
                        (ct.FStar_Syntax_Syntax.flags)
                      else ct.FStar_Syntax_Syntax.flags in
                    let uu___2 = ct in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___2.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name = pure_eff;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___2.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___2.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None ->
                    let ct2 =
                      FStar_TypeChecker_Env.unfold_effect_abbrev env1 c in
                    let uu___2 = ct2 in
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        (uu___2.FStar_Syntax_Syntax.comp_univs);
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_PURE_lid;
                      FStar_Syntax_Syntax.result_typ =
                        (uu___2.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___2.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___2.FStar_Syntax_Syntax.flags)
                    } in
              let uu___1 = c in
              {
                FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
                FStar_Syntax_Syntax.pos = (uu___1.FStar_Syntax_Syntax.pos);
                FStar_Syntax_Syntax.vars = (uu___1.FStar_Syntax_Syntax.vars)
              }
            else c
        | uu___ -> c
let (ghost_to_pure_lcomp_aux :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env1 ->
    fun non_informative_only ->
      fun lc ->
        let uu___ =
          (FStar_Syntax_Util.is_ghost_effect
             lc.FStar_TypeChecker_Common.eff_name)
            &&
            (maybe_promote_t env1 non_informative_only
               lc.FStar_TypeChecker_Common.res_typ) in
        if uu___
        then
          let uu___1 =
            downgrade_ghost_effect_name lc.FStar_TypeChecker_Common.eff_name in
          match uu___1 with
          | FStar_Pervasives_Native.Some pure_eff ->
              let uu___2 =
                FStar_TypeChecker_Common.apply_lcomp
                  (ghost_to_pure_aux env1 non_informative_only) (fun g -> g)
                  lc in
              {
                FStar_TypeChecker_Common.eff_name = pure_eff;
                FStar_TypeChecker_Common.res_typ =
                  (uu___2.FStar_TypeChecker_Common.res_typ);
                FStar_TypeChecker_Common.cflags =
                  (uu___2.FStar_TypeChecker_Common.cflags);
                FStar_TypeChecker_Common.comp_thunk =
                  (uu___2.FStar_TypeChecker_Common.comp_thunk)
              }
          | FStar_Pervasives_Native.None -> lc
        else lc
let (maybe_ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  = fun env1 -> fun c -> ghost_to_pure_aux env1 true c
let (maybe_ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  = fun env1 -> fun lc -> ghost_to_pure_lcomp_aux env1 true lc
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  = fun env1 -> fun c -> ghost_to_pure_aux env1 false c
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  = fun env1 -> fun lc -> ghost_to_pure_lcomp_aux env1 false lc
let (ghost_to_pure2 :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.comp) ->
      (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.comp))
  =
  fun env1 ->
    fun uu___ ->
      match uu___ with
      | (c1, c2) ->
          let uu___1 =
            let uu___2 = maybe_ghost_to_pure env1 c1 in
            let uu___3 = maybe_ghost_to_pure env1 c2 in (uu___2, uu___3) in
          (match uu___1 with
           | (c11, c21) ->
               let c1_eff =
                 let uu___2 =
                   FStar_All.pipe_right c11
                     FStar_Syntax_Util.comp_effect_name in
                 FStar_All.pipe_right uu___2
                   (FStar_TypeChecker_Env.norm_eff_name env1) in
               let c2_eff =
                 let uu___2 =
                   FStar_All.pipe_right c21
                     FStar_Syntax_Util.comp_effect_name in
                 FStar_All.pipe_right uu___2
                   (FStar_TypeChecker_Env.norm_eff_name env1) in
               let uu___2 = FStar_Ident.lid_equals c1_eff c2_eff in
               if uu___2
               then (c11, c21)
               else
                 (let c1_erasable =
                    FStar_TypeChecker_Env.is_erasable_effect env1 c1_eff in
                  let c2_erasable =
                    FStar_TypeChecker_Env.is_erasable_effect env1 c2_eff in
                  let uu___4 =
                    c1_erasable &&
                      (FStar_Ident.lid_equals c2_eff
                         FStar_Parser_Const.effect_GHOST_lid) in
                  if uu___4
                  then let uu___5 = ghost_to_pure env1 c21 in (c11, uu___5)
                  else
                    (let uu___6 =
                       c2_erasable &&
                         (FStar_Ident.lid_equals c1_eff
                            FStar_Parser_Const.effect_GHOST_lid) in
                     if uu___6
                     then
                       let uu___7 = ghost_to_pure env1 c11 in (uu___7, c21)
                     else (c11, c21))))
let (ghost_to_pure_lcomp2 :
  FStar_TypeChecker_Env.env ->
    (FStar_TypeChecker_Common.lcomp * FStar_TypeChecker_Common.lcomp) ->
      (FStar_TypeChecker_Common.lcomp * FStar_TypeChecker_Common.lcomp))
  =
  fun env1 ->
    fun uu___ ->
      match uu___ with
      | (lc1, lc2) ->
          let uu___1 =
            let uu___2 = maybe_ghost_to_pure_lcomp env1 lc1 in
            let uu___3 = maybe_ghost_to_pure_lcomp env1 lc2 in
            (uu___2, uu___3) in
          (match uu___1 with
           | (lc11, lc21) ->
               let lc1_eff =
                 FStar_TypeChecker_Env.norm_eff_name env1
                   lc11.FStar_TypeChecker_Common.eff_name in
               let lc2_eff =
                 FStar_TypeChecker_Env.norm_eff_name env1
                   lc21.FStar_TypeChecker_Common.eff_name in
               let uu___2 = FStar_Ident.lid_equals lc1_eff lc2_eff in
               if uu___2
               then (lc11, lc21)
               else
                 (let lc1_erasable =
                    FStar_TypeChecker_Env.is_erasable_effect env1 lc1_eff in
                  let lc2_erasable =
                    FStar_TypeChecker_Env.is_erasable_effect env1 lc2_eff in
                  let uu___4 =
                    lc1_erasable &&
                      (FStar_Ident.lid_equals lc2_eff
                         FStar_Parser_Const.effect_GHOST_lid) in
                  if uu___4
                  then
                    let uu___5 = ghost_to_pure_lcomp env1 lc21 in
                    (lc11, uu___5)
                  else
                    (let uu___6 =
                       lc2_erasable &&
                         (FStar_Ident.lid_equals lc1_eff
                            FStar_Parser_Const.effect_GHOST_lid) in
                     if uu___6
                     then
                       let uu___7 = ghost_to_pure_lcomp env1 lc11 in
                       (uu___7, lc21)
                     else (lc11, lc21))))
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env1 ->
    fun t ->
      let t1 =
        try
          (fun uu___ ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env1
                   t) ()
        with
        | uu___ ->
            ((let uu___2 =
                let uu___3 =
                  let uu___4 = FStar_Util.message_of_exn uu___ in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu___4 in
                (FStar_Errors.Warning_NormalizationFailure, uu___3) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu___2);
             t) in
      FStar_Syntax_Print.term_to_string' env1.FStar_TypeChecker_Env.dsenv t1
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env1 ->
    fun c ->
      let c1 =
        try
          (fun uu___ ->
             match () with
             | () ->
                 let uu___1 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env1 in
                 norm_comp uu___1 [] c) ()
        with
        | uu___ ->
            ((let uu___2 =
                let uu___3 =
                  let uu___4 = FStar_Util.message_of_exn uu___ in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu___4 in
                (FStar_Errors.Warning_NormalizationFailure, uu___3) in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu___2);
             c) in
      FStar_Syntax_Print.comp_to_string' env1.FStar_TypeChecker_Env.dsenv c1
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun steps ->
    fun env1 ->
      fun t0 ->
        let t =
          normalize (FStar_List.append steps [FStar_TypeChecker_Env.Beta])
            env1 t0 in
        let rec aux t1 =
          let t2 = FStar_Syntax_Subst.compress t1 in
          match t2.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x, phi) ->
              let t01 = aux x.FStar_Syntax_Syntax.sort in
              (match t01.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_refine (y, phi1) ->
                   let uu___ =
                     let uu___1 =
                       let uu___2 = FStar_Syntax_Util.mk_conj_simp phi1 phi in
                       (y, uu___2) in
                     FStar_Syntax_Syntax.Tm_refine uu___1 in
                   FStar_Syntax_Syntax.mk uu___ t01.FStar_Syntax_Syntax.pos
               | uu___ -> t2)
          | uu___ -> t2 in
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
  fun steps ->
    fun env1 ->
      fun t -> normalize (FStar_List.append steps whnf_steps) env1 t
let (unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env1 -> fun t -> unfold_whnf' [] env1 t
let (reduce_or_remove_uvar_solutions :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun remove ->
    fun env1 ->
      fun t ->
        normalize
          (FStar_List.append
             (if remove then [FStar_TypeChecker_Env.CheckNoUvars] else [])
             [FStar_TypeChecker_Env.Beta;
             FStar_TypeChecker_Env.DoNotUnfoldPureLets;
             FStar_TypeChecker_Env.CompressUvars;
             FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
             FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Iota;
             FStar_TypeChecker_Env.NoFullNorm]) env1 t
let (reduce_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env1 -> fun t -> reduce_or_remove_uvar_solutions false env1 t
let (remove_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env1 -> fun t -> reduce_or_remove_uvar_solutions true env1 t
let (eta_expand_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env1 ->
    fun e ->
      fun t_e ->
        let uu___ = FStar_Syntax_Util.arrow_formals_comp t_e in
        match uu___ with
        | (formals, c) ->
            (match formals with
             | [] -> e
             | uu___1 ->
                 let uu___2 = FStar_Syntax_Util.abs_formals e in
                 (match uu___2 with
                  | (actuals, uu___3, uu___4) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu___6 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders in
                         match uu___6 with
                         | (binders, args) ->
                             let uu___7 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 e.FStar_Syntax_Syntax.pos in
                             FStar_Syntax_Util.abs binders uu___7
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
let (eta_expand :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env1 ->
    fun t ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x ->
          eta_expand_with_type env1 t x.FStar_Syntax_Syntax.sort
      | uu___ ->
          let uu___1 = FStar_Syntax_Util.head_and_args t in
          (match uu___1 with
           | (head, args) ->
               let uu___2 =
                 let uu___3 = FStar_Syntax_Subst.compress head in
                 uu___3.FStar_Syntax_Syntax.n in
               (match uu___2 with
                | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
                    let uu___3 =
                      let uu___4 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ in
                      FStar_Syntax_Util.arrow_formals uu___4 in
                    (match uu___3 with
                     | (formals, _tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu___5 =
                              env1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                (let uu___6 = env1 in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___6.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___6.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___6.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___6.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___6.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___6.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___6.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___6.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___6.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___6.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___6.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___6.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___6.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___6.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___6.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___6.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___6.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___6.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___6.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___6.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___6.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___6.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___6.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___6.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___6.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                     =
                                     (uu___6.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___6.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                     =
                                     (uu___6.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___6.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___6.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___6.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___6.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___6.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___6.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___6.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___6.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___6.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___6.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___6.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___6.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___6.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___6.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___6.FStar_TypeChecker_Env.erasable_types_tab);
                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                     =
                                     (uu___6.FStar_TypeChecker_Env.enable_defer_to_tac);
                                   FStar_TypeChecker_Env.unif_allow_ref_guards
                                     =
                                     (uu___6.FStar_TypeChecker_Env.unif_allow_ref_guards)
                                 }) t true in
                            match uu___5 with
                            | (uu___6, ty, uu___7) ->
                                eta_expand_with_type env1 t ty))
                | uu___3 ->
                    let uu___4 =
                      env1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                        (let uu___5 = env1 in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___5.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___5.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___5.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___5.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___5.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___5.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___5.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___5.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___5.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___5.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___5.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___5.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___5.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___5.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___5.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___5.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.use_eq_strict =
                             (uu___5.FStar_TypeChecker_Env.use_eq_strict);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___5.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___5.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___5.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___5.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___5.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___5.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___5.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___5.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                             (uu___5.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___5.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                             =
                             (uu___5.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___5.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___5.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___5.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___5.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___5.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.try_solve_implicits_hook =
                             (uu___5.FStar_TypeChecker_Env.try_solve_implicits_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___5.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.mpreprocess =
                             (uu___5.FStar_TypeChecker_Env.mpreprocess);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___5.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___5.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___5.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___5.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___5.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___5.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___5.FStar_TypeChecker_Env.erasable_types_tab);
                           FStar_TypeChecker_Env.enable_defer_to_tac =
                             (uu___5.FStar_TypeChecker_Env.enable_defer_to_tac);
                           FStar_TypeChecker_Env.unif_allow_ref_guards =
                             (uu___5.FStar_TypeChecker_Env.unif_allow_ref_guards)
                         }) t true in
                    (match uu___4 with
                     | (uu___5, ty, uu___6) -> eta_expand_with_type env1 t ty)))
let (elim_uvars_aux_tc :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.comp)
          FStar_Pervasives.either ->
          (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.binder
            Prims.list *
            (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
            FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
            FStar_Pervasives.either))
  =
  fun env1 ->
    fun univ_names ->
      fun binders ->
        fun tc ->
          let t =
            match (binders, tc) with
            | ([], FStar_Pervasives.Inl t1) -> t1
            | ([], FStar_Pervasives.Inr c) ->
                failwith "Impossible: empty bindes with a comp"
            | (uu___, FStar_Pervasives.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  c.FStar_Syntax_Syntax.pos
            | (uu___, FStar_Pervasives.Inl t1) ->
                let uu___1 =
                  let uu___2 =
                    let uu___3 = FStar_Syntax_Syntax.mk_Total t1 in
                    (binders, uu___3) in
                  FStar_Syntax_Syntax.Tm_arrow uu___2 in
                FStar_Syntax_Syntax.mk uu___1 t1.FStar_Syntax_Syntax.pos in
          let uu___ = FStar_Syntax_Subst.open_univ_vars univ_names t in
          match uu___ with
          | (univ_names1, t1) ->
              let t2 = remove_uvar_solutions env1 t1 in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let t4 = FStar_Syntax_Subst.deep_compress t3 in
              let uu___1 =
                match binders with
                | [] -> ([], (FStar_Pervasives.Inl t4))
                | uu___2 ->
                    let uu___3 =
                      let uu___4 =
                        let uu___5 = FStar_Syntax_Subst.compress t4 in
                        uu___5.FStar_Syntax_Syntax.n in
                      (uu___4, tc) in
                    (match uu___3 with
                     | (FStar_Syntax_Syntax.Tm_arrow (binders1, c),
                        FStar_Pervasives.Inr uu___4) ->
                         (binders1, (FStar_Pervasives.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow (binders1, c),
                        FStar_Pervasives.Inl uu___4) ->
                         (binders1,
                           (FStar_Pervasives.Inl
                              (FStar_Syntax_Util.comp_result c)))
                     | (uu___4, FStar_Pervasives.Inl uu___5) ->
                         ([], (FStar_Pervasives.Inl t4))
                     | uu___4 -> failwith "Impossible") in
              (match uu___1 with
               | (binders1, tc1) -> (univ_names1, binders1, tc1))
let (elim_uvars_aux_t :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.binder
            Prims.list * FStar_Syntax_Syntax.term'
            FStar_Syntax_Syntax.syntax))
  =
  fun env1 ->
    fun univ_names ->
      fun binders ->
        fun t ->
          let uu___ =
            elim_uvars_aux_tc env1 univ_names binders
              (FStar_Pervasives.Inl t) in
          match uu___ with
          | (univ_names1, binders1, tc) ->
              let uu___1 = FStar_Util.left tc in
              (univ_names1, binders1, uu___1)
let (elim_uvars_aux_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.binder
            Prims.list * FStar_Syntax_Syntax.comp'
            FStar_Syntax_Syntax.syntax))
  =
  fun env1 ->
    fun univ_names ->
      fun binders ->
        fun c ->
          let uu___ =
            elim_uvars_aux_tc env1 univ_names binders
              (FStar_Pervasives.Inr c) in
          match uu___ with
          | (univ_names1, binders1, tc) ->
              let uu___1 = FStar_Util.right tc in
              (univ_names1, binders1, uu___1)
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env1 ->
    fun s ->
      let s1 =
        let uu___ = s in
        let uu___1 =
          FStar_List.map FStar_Syntax_Subst.deep_compress
            s.FStar_Syntax_Syntax.sigattrs in
        {
          FStar_Syntax_Syntax.sigel = (uu___.FStar_Syntax_Syntax.sigel);
          FStar_Syntax_Syntax.sigrng = (uu___.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals = (uu___.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta = (uu___.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs = uu___1;
          FStar_Syntax_Syntax.sigopts = (uu___.FStar_Syntax_Syntax.sigopts)
        } in
      match s1.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid, univ_names, binders, typ, lids, lids') ->
          let uu___ = elim_uvars_aux_t env1 univ_names binders typ in
          (match uu___ with
           | (univ_names1, binders1, typ1) ->
               let uu___1 = s1 in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___1.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___1.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___1.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___1.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___1.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs, lids) ->
          let uu___ = s1 in
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_List.map (elim_uvars env1) sigs in
              (uu___3, lids) in
            FStar_Syntax_Syntax.Sig_bundle uu___2 in
          {
            FStar_Syntax_Syntax.sigel = uu___1;
            FStar_Syntax_Syntax.sigrng = (uu___.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta = (uu___.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts = (uu___.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_datacon
          (lid, univ_names, typ, lident, i, lids) ->
          let uu___ = elim_uvars_aux_t env1 univ_names [] typ in
          (match uu___ with
           | (univ_names1, uu___1, typ1) ->
               let uu___2 = s1 in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___2.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___2.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___2.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___2.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___2.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, univ_names, typ) ->
          let uu___ = elim_uvars_aux_t env1 univ_names [] typ in
          (match uu___ with
           | (univ_names1, uu___1, typ1) ->
               let uu___2 = s1 in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___2.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___2.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___2.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___2.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___2.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb ->
                    let uu___ =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs in
                    match uu___ with
                    | (opening, lbunivs) ->
                        let elim t =
                          let uu___1 =
                            let uu___2 =
                              let uu___3 = FStar_Syntax_Subst.subst opening t in
                              remove_uvar_solutions env1 uu___3 in
                            FStar_Syntax_Subst.close_univ_vars lbunivs uu___2 in
                          FStar_Syntax_Subst.deep_compress uu___1 in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef in
                        let uu___1 = lb in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___1.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___1.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___1.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___1.FStar_Syntax_Syntax.lbpos)
                        })) in
          let uu___ = s1 in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng = (uu___.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta = (uu___.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts = (uu___.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_assume (l, us, t) ->
          let uu___ = elim_uvars_aux_t env1 us [] t in
          (match uu___ with
           | (us1, uu___1, t1) ->
               let uu___2 = s1 in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___2.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___2.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___2.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___2.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___2.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu___ =
            elim_uvars_aux_t env1 ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit in
          (match uu___ with
           | (univs, binders, uu___1) ->
               let uu___2 =
                 let uu___3 = FStar_Syntax_Subst.univ_var_opening univs in
                 match uu___3 with
                 | (univs_opening, univs1) ->
                     let uu___4 = FStar_Syntax_Subst.univ_var_closing univs1 in
                     (univs_opening, uu___4) in
               (match uu___2 with
                | (univs_opening, univs_closing) ->
                    let uu___3 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders in
                      let uu___4 =
                        FStar_Syntax_Subst.opening_of_binders binders1 in
                      let uu___5 =
                        FStar_Syntax_Subst.closing_of_binders binders1 in
                      (uu___4, uu___5) in
                    (match uu___3 with
                     | (b_opening, b_closing) ->
                         let n = FStar_List.length univs in
                         let n_binders = FStar_List.length binders in
                         let elim_tscheme uu___4 =
                           match uu___4 with
                           | (us, t) ->
                               let n_us = FStar_List.length us in
                               let uu___5 =
                                 FStar_Syntax_Subst.open_univ_vars us t in
                               (match uu___5 with
                                | (us1, t1) ->
                                    let uu___6 =
                                      let uu___7 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      let uu___8 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us) in
                                      (uu___7, uu___8) in
                                    (match uu___6 with
                                     | (b_opening1, b_closing1) ->
                                         let uu___7 =
                                           let uu___8 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders)) in
                                           let uu___9 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders)) in
                                           (uu___8, uu___9) in
                                         (match uu___7 with
                                          | (univs_opening1, univs_closing1)
                                              ->
                                              let t2 =
                                                let uu___8 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu___8 in
                                              let uu___8 =
                                                elim_uvars_aux_t env1 [] []
                                                  t2 in
                                              (match uu___8 with
                                               | (uu___9, uu___10, t3) ->
                                                   let t4 =
                                                     let uu___11 =
                                                       let uu___12 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1 uu___12 in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1 uu___11 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu___4 = elim_uvars_aux_t env1 univs binders t in
                           match uu___4 with | (uu___5, uu___6, t1) -> t1 in
                         let elim_action a =
                           let action_typ_templ =
                             let body =
                               FStar_Syntax_Syntax.mk
                                 (FStar_Syntax_Syntax.Tm_ascribed
                                    ((a.FStar_Syntax_Syntax.action_defn),
                                      ((FStar_Pervasives.Inl
                                          (a.FStar_Syntax_Syntax.action_typ)),
                                        FStar_Pervasives_Native.None),
                                      FStar_Pervasives_Native.None))
                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                             match a.FStar_Syntax_Syntax.action_params with
                             | [] -> body
                             | uu___4 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu___4 =
                               let uu___5 = FStar_Syntax_Subst.compress body in
                               uu___5.FStar_Syntax_Syntax.n in
                             match uu___4 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,
                                  (FStar_Pervasives.Inl typ,
                                   FStar_Pervasives_Native.None),
                                  FStar_Pervasives_Native.None)
                                 -> (defn, typ)
                             | uu___5 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu___4 =
                               let uu___5 = FStar_Syntax_Subst.compress t in
                               uu___5.FStar_Syntax_Syntax.n in
                             match uu___4 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars, body, uu___5) ->
                                 let uu___6 = destruct_action_body body in
                                 (match uu___6 with
                                  | (defn, typ) -> (pars, defn, typ))
                             | uu___5 ->
                                 let uu___6 = destruct_action_body t in
                                 (match uu___6 with
                                  | (defn, typ) -> ([], defn, typ)) in
                           let uu___4 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu___4 with
                           | (action_univs, t) ->
                               let uu___5 = destruct_action_typ_templ t in
                               (match uu___5 with
                                | (action_params, action_defn, action_typ) ->
                                    let a' =
                                      let uu___6 = a in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___6.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___6.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          action_univs;
                                        FStar_Syntax_Syntax.action_params =
                                          action_params;
                                        FStar_Syntax_Syntax.action_defn =
                                          action_defn;
                                        FStar_Syntax_Syntax.action_typ =
                                          action_typ
                                      } in
                                    a') in
                         let ed1 =
                           let uu___4 = ed in
                           let uu___5 =
                             elim_tscheme ed.FStar_Syntax_Syntax.signature in
                           let uu___6 =
                             FStar_Syntax_Util.apply_eff_combinators
                               elim_tscheme
                               ed.FStar_Syntax_Syntax.combinators in
                           let uu___7 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.mname =
                               (uu___4.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___4.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.univs = univs;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = uu___5;
                             FStar_Syntax_Syntax.combinators = uu___6;
                             FStar_Syntax_Syntax.actions = uu___7;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___4.FStar_Syntax_Syntax.eff_attrs)
                           } in
                         let uu___4 = s1 in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___4.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___4.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___4.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___4.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___4.FStar_Syntax_Syntax.sigopts)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___ =
            match uu___ with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us, t) ->
                let uu___1 = elim_uvars_aux_t env1 us [] t in
                (match uu___1 with
                 | (us1, uu___2, t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___ = sub_eff in
            let uu___1 = elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp in
            let uu___2 = elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift in
            {
              FStar_Syntax_Syntax.source = (uu___.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target = (uu___.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu___1;
              FStar_Syntax_Syntax.lift = uu___2
            } in
          let uu___ = s1 in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng = (uu___.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta = (uu___.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts = (uu___.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid, univ_names, binders, comp, flags) ->
          let uu___ = elim_uvars_aux_c env1 univ_names binders comp in
          (match uu___ with
           | (univ_names1, binders1, comp1) ->
               let uu___1 = s1 in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___1.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___1.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___1.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___1.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___1.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu___ -> s1
      | FStar_Syntax_Syntax.Sig_fail uu___ -> s1
      | FStar_Syntax_Syntax.Sig_splice uu___ -> s1
      | FStar_Syntax_Syntax.Sig_polymonadic_bind
          (m, n, p, (us_t, t), (us_ty, ty)) ->
          let uu___ = elim_uvars_aux_t env1 us_t [] t in
          (match uu___ with
           | (us_t1, uu___1, t1) ->
               let uu___2 = elim_uvars_aux_t env1 us_ty [] ty in
               (match uu___2 with
                | (us_ty1, uu___3, ty1) ->
                    let uu___4 = s1 in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_polymonadic_bind
                           (m, n, p, (us_t1, t1), (us_ty1, ty1)));
                      FStar_Syntax_Syntax.sigrng =
                        (uu___4.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___4.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___4.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___4.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___4.FStar_Syntax_Syntax.sigopts)
                    }))
      | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
          (m, n, (us_t, t), (us_ty, ty)) ->
          let uu___ = elim_uvars_aux_t env1 us_t [] t in
          (match uu___ with
           | (us_t1, uu___1, t1) ->
               let uu___2 = elim_uvars_aux_t env1 us_ty [] ty in
               (match uu___2 with
                | (us_ty1, uu___3, ty1) ->
                    let uu___4 = s1 in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                           (m, n, (us_t1, t1), (us_ty1, ty1)));
                      FStar_Syntax_Syntax.sigrng =
                        (uu___4.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___4.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___4.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___4.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___4.FStar_Syntax_Syntax.sigopts)
                    }))
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env1 ->
    fun t ->
      normalize
        [FStar_TypeChecker_Env.EraseUniverses;
        FStar_TypeChecker_Env.AllowUnboundUniverses] env1 t
let (unfold_head_once :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun t ->
      let aux f us args =
        let uu___ =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env1 (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        match uu___ with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu___1 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us in
            (match uu___1 with
             | (uu___2, head_def) ->
                 let t' =
                   FStar_Syntax_Syntax.mk_Tm_app head_def args
                     t.FStar_Syntax_Syntax.pos in
                 let t'1 =
                   normalize
                     [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota]
                     env1 t' in
                 FStar_Pervasives_Native.Some t'1) in
      let uu___ = FStar_Syntax_Util.head_and_args t in
      match uu___ with
      | (head, args) ->
          let uu___1 =
            let uu___2 = FStar_Syntax_Subst.compress head in
            uu___2.FStar_Syntax_Syntax.n in
          (match uu___1 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu___2;
                  FStar_Syntax_Syntax.vars = uu___3;_},
                us)
               -> aux fv us args
           | uu___2 -> FStar_Pervasives_Native.None)
let (get_n_binders :
  FStar_TypeChecker_Env.env ->
    Prims.int ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.binder Prims.list * FStar_Syntax_Syntax.comp))
  =
  fun env1 ->
    fun n ->
      fun t ->
        let rec aux retry n1 t1 =
          let uu___ = FStar_Syntax_Util.arrow_formals_comp t1 in
          match uu___ with
          | (bs, c) ->
              let len = FStar_List.length bs in
              (match (bs, c) with
               | ([], uu___1) when retry ->
                   let uu___2 = unfold_whnf env1 t1 in aux false n1 uu___2
               | ([], uu___1) when Prims.op_Negation retry -> (bs, c)
               | (bs1, c1) when len = n1 -> (bs1, c1)
               | (bs1, c1) when len > n1 ->
                   let uu___1 = FStar_List.splitAt n1 bs1 in
                   (match uu___1 with
                    | (bs_l, bs_r) ->
                        let uu___2 =
                          let uu___3 = FStar_Syntax_Util.arrow bs_r c1 in
                          FStar_Syntax_Syntax.mk_Total uu___3 in
                        (bs_l, uu___2))
               | (bs1, c1) when
                   ((len < n1) && (FStar_Syntax_Util.is_total_comp c1)) &&
                     (let uu___1 = FStar_Syntax_Util.has_decreases c1 in
                      Prims.op_Negation uu___1)
                   ->
                   let uu___1 =
                     aux true (n1 - len) (FStar_Syntax_Util.comp_result c1) in
                   (match uu___1 with
                    | (bs', c') -> ((FStar_List.append bs1 bs'), c'))
               | (bs1, c1) -> (bs1, c1)) in
        aux true n t