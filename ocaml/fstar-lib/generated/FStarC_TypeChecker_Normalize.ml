open Prims
let (dbg_univ_norm : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "univ_norm"
let (dbg_NormRebuild : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "NormRebuild"
let (maybe_debug :
  FStarC_TypeChecker_Cfg.cfg ->
    FStarC_Syntax_Syntax.term ->
      (FStarC_Syntax_Syntax.term * FStarC_Compiler_Util.time)
        FStar_Pervasives_Native.option -> unit)
  =
  fun cfg ->
    fun t ->
      fun dbg ->
        if
          (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.print_normalized
        then
          match dbg with
          | FStar_Pervasives_Native.Some (tm, time_then) ->
              let time_now = FStarC_Compiler_Util.now () in
              let uu___ =
                let uu___1 =
                  let uu___2 =
                    FStarC_Compiler_Util.time_diff time_then time_now in
                  FStar_Pervasives_Native.snd uu___2 in
                FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___1 in
              let uu___1 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term tm in
              let uu___2 =
                FStarC_Class_Show.show FStarC_TypeChecker_Cfg.showable_cfg
                  cfg in
              let uu___3 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
              FStarC_Compiler_Util.print4
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
type 'a cfg_memo =
  (FStarC_TypeChecker_Cfg.cfg * 'a) FStarC_Syntax_Syntax.memo
let fresh_memo : 'a . unit -> 'a FStarC_Syntax_Syntax.memo =
  fun uu___ -> FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None
type closure =
  | Clos of ((FStarC_Syntax_Syntax.binder FStar_Pervasives_Native.option *
  closure * FStarC_Syntax_Syntax.subst_t FStarC_Syntax_Syntax.memo)
  Prims.list * FStarC_Syntax_Syntax.term * ((FStarC_Syntax_Syntax.binder
  FStar_Pervasives_Native.option * closure * FStarC_Syntax_Syntax.subst_t
  FStarC_Syntax_Syntax.memo) Prims.list * FStarC_Syntax_Syntax.term) cfg_memo
  * Prims.bool) 
  | Univ of FStarC_Syntax_Syntax.universe 
  | Dummy 
let (uu___is_Clos : closure -> Prims.bool) =
  fun projectee -> match projectee with | Clos _0 -> true | uu___ -> false
let (__proj__Clos__item___0 :
  closure ->
    ((FStarC_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure *
      FStarC_Syntax_Syntax.subst_t FStarC_Syntax_Syntax.memo) Prims.list *
      FStarC_Syntax_Syntax.term * ((FStarC_Syntax_Syntax.binder
      FStar_Pervasives_Native.option * closure * FStarC_Syntax_Syntax.subst_t
      FStarC_Syntax_Syntax.memo) Prims.list * FStarC_Syntax_Syntax.term)
      cfg_memo * Prims.bool))
  = fun projectee -> match projectee with | Clos _0 -> _0
let (uu___is_Univ : closure -> Prims.bool) =
  fun projectee -> match projectee with | Univ _0 -> true | uu___ -> false
let (__proj__Univ__item___0 : closure -> FStarC_Syntax_Syntax.universe) =
  fun projectee -> match projectee with | Univ _0 -> _0
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee -> match projectee with | Dummy -> true | uu___ -> false
type env =
  (FStarC_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure *
    FStarC_Syntax_Syntax.subst_t FStarC_Syntax_Syntax.memo) Prims.list
let showable_memo :
  'a .
    'a FStarC_Class_Show.showable ->
      'a FStarC_Syntax_Syntax.memo FStarC_Class_Show.showable
  =
  fun uu___ ->
    {
      FStarC_Class_Show.show =
        (fun m ->
           let uu___1 = FStarC_Compiler_Effect.op_Bang m in
           match uu___1 with
           | FStar_Pervasives_Native.None -> "no_memo"
           | FStar_Pervasives_Native.Some x ->
               let uu___2 = FStarC_Class_Show.show uu___ x in
               Prims.strcat "memo=" uu___2)
    }
let (empty_env : env) = []
let (dummy :
  unit ->
    (FStarC_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure *
      FStarC_Syntax_Syntax.subst_t FStarC_Syntax_Syntax.memo))
  =
  fun uu___ ->
    let uu___1 = fresh_memo () in
    (FStar_Pervasives_Native.None, Dummy, uu___1)
type branches =
  (FStarC_Syntax_Syntax.pat * FStarC_Syntax_Syntax.term
    FStar_Pervasives_Native.option * FStarC_Syntax_Syntax.term) Prims.list
type stack_elt =
  | Arg of (closure * FStarC_Syntax_Syntax.aqual *
  FStarC_Compiler_Range_Type.range) 
  | UnivArgs of (FStarC_Syntax_Syntax.universe Prims.list *
  FStarC_Compiler_Range_Type.range) 
  | MemoLazy of (env * FStarC_Syntax_Syntax.term) cfg_memo 
  | Match of (env * FStarC_Syntax_Syntax.match_returns_ascription
  FStar_Pervasives_Native.option * branches *
  FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
  FStarC_TypeChecker_Cfg.cfg * FStarC_Compiler_Range_Type.range) 
  | Abs of (env * FStarC_Syntax_Syntax.binders * env *
  FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
  FStarC_Compiler_Range_Type.range) 
  | App of (env * FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.aqual *
  FStarC_Compiler_Range_Type.range) 
  | CBVApp of (env * FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.aqual *
  FStarC_Compiler_Range_Type.range) 
  | Meta of (env * FStarC_Syntax_Syntax.metadata *
  FStarC_Compiler_Range_Type.range) 
  | Let of (env * FStarC_Syntax_Syntax.binders *
  FStarC_Syntax_Syntax.letbinding * FStarC_Compiler_Range_Type.range) 
let (uu___is_Arg : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | Arg _0 -> true | uu___ -> false
let (__proj__Arg__item___0 :
  stack_elt ->
    (closure * FStarC_Syntax_Syntax.aqual * FStarC_Compiler_Range_Type.range))
  = fun projectee -> match projectee with | Arg _0 -> _0
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | UnivArgs _0 -> true | uu___ -> false
let (__proj__UnivArgs__item___0 :
  stack_elt ->
    (FStarC_Syntax_Syntax.universe Prims.list *
      FStarC_Compiler_Range_Type.range))
  = fun projectee -> match projectee with | UnivArgs _0 -> _0
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee ->
    match projectee with | MemoLazy _0 -> true | uu___ -> false
let (__proj__MemoLazy__item___0 :
  stack_elt -> (env * FStarC_Syntax_Syntax.term) cfg_memo) =
  fun projectee -> match projectee with | MemoLazy _0 -> _0
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | Match _0 -> true | uu___ -> false
let (__proj__Match__item___0 :
  stack_elt ->
    (env * FStarC_Syntax_Syntax.match_returns_ascription
      FStar_Pervasives_Native.option * branches *
      FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
      FStarC_TypeChecker_Cfg.cfg * FStarC_Compiler_Range_Type.range))
  = fun projectee -> match projectee with | Match _0 -> _0
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | Abs _0 -> true | uu___ -> false
let (__proj__Abs__item___0 :
  stack_elt ->
    (env * FStarC_Syntax_Syntax.binders * env *
      FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
      FStarC_Compiler_Range_Type.range))
  = fun projectee -> match projectee with | Abs _0 -> _0
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | App _0 -> true | uu___ -> false
let (__proj__App__item___0 :
  stack_elt ->
    (env * FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.aqual *
      FStarC_Compiler_Range_Type.range))
  = fun projectee -> match projectee with | App _0 -> _0
let (uu___is_CBVApp : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | CBVApp _0 -> true | uu___ -> false
let (__proj__CBVApp__item___0 :
  stack_elt ->
    (env * FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.aqual *
      FStarC_Compiler_Range_Type.range))
  = fun projectee -> match projectee with | CBVApp _0 -> _0
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | Meta _0 -> true | uu___ -> false
let (__proj__Meta__item___0 :
  stack_elt ->
    (env * FStarC_Syntax_Syntax.metadata * FStarC_Compiler_Range_Type.range))
  = fun projectee -> match projectee with | Meta _0 -> _0
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee -> match projectee with | Let _0 -> true | uu___ -> false
let (__proj__Let__item___0 :
  stack_elt ->
    (env * FStarC_Syntax_Syntax.binders * FStarC_Syntax_Syntax.letbinding *
      FStarC_Compiler_Range_Type.range))
  = fun projectee -> match projectee with | Let _0 -> _0
type stack = stack_elt Prims.list
let (head_of : FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) =
  fun t ->
    let uu___ = FStarC_Syntax_Util.head_and_args_full t in
    match uu___ with | (hd, uu___1) -> hd
let (cfg_equivalent :
  FStarC_TypeChecker_Cfg.cfg -> FStarC_TypeChecker_Cfg.cfg -> Prims.bool) =
  fun c1 ->
    fun c2 ->
      ((FStarC_Class_Deq.op_Equals_Question FStarC_TypeChecker_Cfg.deq_fsteps
          c1.FStarC_TypeChecker_Cfg.steps c2.FStarC_TypeChecker_Cfg.steps)
         &&
         (FStarC_Class_Deq.op_Equals_Question
            (FStarC_Class_Deq.deq_list FStarC_TypeChecker_Env.deq_delta_level)
            c1.FStarC_TypeChecker_Cfg.delta_level
            c2.FStarC_TypeChecker_Cfg.delta_level))
        &&
        (FStarC_Class_Deq.op_Equals_Question
           (FStarC_Class_Ord.ord_eq FStarC_Class_Ord.ord_bool)
           c1.FStarC_TypeChecker_Cfg.normalize_pure_lets
           c2.FStarC_TypeChecker_Cfg.normalize_pure_lets)
let read_memo :
  'a .
    FStarC_TypeChecker_Cfg.cfg ->
      (FStarC_TypeChecker_Cfg.cfg * 'a) FStarC_Syntax_Syntax.memo ->
        'a FStar_Pervasives_Native.option
  =
  fun cfg ->
    fun r ->
      let uu___ = FStarC_Compiler_Effect.op_Bang r in
      match uu___ with
      | FStar_Pervasives_Native.Some (cfg', a1) when
          (cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg ||
             (FStarC_Compiler_Util.physical_equality cfg cfg'))
            || (cfg_equivalent cfg' cfg)
          -> FStar_Pervasives_Native.Some a1
      | uu___1 -> FStar_Pervasives_Native.None
let set_memo :
  'a .
    FStarC_TypeChecker_Cfg.cfg ->
      (FStarC_TypeChecker_Cfg.cfg * 'a) FStarC_Syntax_Syntax.memo ->
        'a -> unit
  =
  fun cfg ->
    fun r ->
      fun t ->
        if cfg.FStarC_TypeChecker_Cfg.memoize_lazy
        then
          ((let uu___1 =
              let uu___2 = read_memo cfg r in
              FStarC_Compiler_Option.isSome uu___2 in
            if uu___1
            then failwith "Unexpected set_memo: thunk already evaluated"
            else ());
           FStarC_Compiler_Effect.op_Colon_Equals r
             (FStar_Pervasives_Native.Some (cfg, t)))
        else ()
let (closure_to_string : closure -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | Clos (env1, t, uu___1, uu___2) ->
        let uu___3 =
          FStarC_Compiler_Util.string_of_int
            (FStarC_Compiler_List.length env1) in
        let uu___4 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
        FStarC_Compiler_Util.format2 "(env=%s elts; %s)" uu___3 uu___4
    | Univ uu___1 -> "Univ"
    | Dummy -> "dummy"
let (showable_closure : closure FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = closure_to_string }
let (showable_stack_elt : stack_elt FStarC_Class_Show.showable) =
  {
    FStarC_Class_Show.show =
      (fun uu___ ->
         match uu___ with
         | Arg (c, uu___1, uu___2) ->
             let uu___3 = FStarC_Class_Show.show showable_closure c in
             FStarC_Compiler_Util.format1 "Closure %s" uu___3
         | MemoLazy uu___1 -> "MemoLazy"
         | Abs (uu___1, bs, uu___2, uu___3, uu___4) ->
             let uu___5 =
               FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                 (FStarC_Compiler_List.length bs) in
             FStarC_Compiler_Util.format1 "Abs %s" uu___5
         | UnivArgs uu___1 -> "UnivArgs"
         | Match uu___1 -> "Match"
         | App (uu___1, t, uu___2, uu___3) ->
             let uu___4 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
             FStarC_Compiler_Util.format1 "App %s" uu___4
         | CBVApp (uu___1, t, uu___2, uu___3) ->
             let uu___4 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
             FStarC_Compiler_Util.format1 "CBVApp %s" uu___4
         | Meta (uu___1, m, uu___2) -> "Meta"
         | Let uu___1 -> "Let")
  }
let is_empty : 'uuuuu . 'uuuuu Prims.list -> Prims.bool =
  fun uu___ -> match uu___ with | [] -> true | uu___1 -> false
let (lookup_bvar : env -> FStarC_Syntax_Syntax.bv -> closure) =
  fun env1 ->
    fun x ->
      try
        (fun uu___ ->
           match () with
           | () ->
               let uu___1 =
                 FStarC_Compiler_List.nth env1 x.FStarC_Syntax_Syntax.index in
               FStar_Pervasives_Native.__proj__Mktuple3__item___2 uu___1) ()
      with
      | uu___ ->
          let uu___1 =
            let uu___2 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_bv x in
            let uu___3 =
              FStarC_Class_Show.show
                (FStarC_Class_Show.show_list
                   (FStarC_Class_Show.show_tuple3
                      (FStarC_Class_Show.show_option
                         FStarC_Syntax_Print.showable_binder)
                      showable_closure
                      (showable_memo
                         (FStarC_Class_Show.show_list
                            FStarC_Syntax_Print.showable_subst_elt)))) env1 in
            FStarC_Compiler_Util.format2 "Failed to find %s\nEnv is %s\n"
              uu___2 uu___3 in
          failwith uu___1
let (downgrade_ghost_effect_name :
  FStarC_Ident.lident -> FStarC_Ident.lident FStar_Pervasives_Native.option)
  =
  fun l ->
    let uu___ =
      FStarC_Ident.lid_equals l FStarC_Parser_Const.effect_Ghost_lid in
    if uu___
    then FStar_Pervasives_Native.Some FStarC_Parser_Const.effect_Pure_lid
    else
      (let uu___2 =
         FStarC_Ident.lid_equals l FStarC_Parser_Const.effect_GTot_lid in
       if uu___2
       then FStar_Pervasives_Native.Some FStarC_Parser_Const.effect_Tot_lid
       else
         (let uu___4 =
            FStarC_Ident.lid_equals l FStarC_Parser_Const.effect_GHOST_lid in
          if uu___4
          then
            FStar_Pervasives_Native.Some FStarC_Parser_Const.effect_PURE_lid
          else FStar_Pervasives_Native.None))
let (norm_universe :
  FStarC_TypeChecker_Cfg.cfg ->
    env -> FStarC_Syntax_Syntax.universe -> FStarC_Syntax_Syntax.universe)
  =
  fun cfg ->
    fun env1 ->
      fun u ->
        let norm_univs_for_max us =
          let us1 =
            FStarC_Compiler_Util.sort_with FStarC_Syntax_Util.compare_univs
              us in
          let uu___ =
            FStarC_Compiler_List.fold_left
              (fun uu___1 ->
                 fun u1 ->
                   match uu___1 with
                   | (cur_kernel, cur_max, out) ->
                       let uu___2 = FStarC_Syntax_Util.univ_kernel u1 in
                       (match uu___2 with
                        | (k_u, n) ->
                            let uu___3 =
                              FStarC_Syntax_Util.eq_univs cur_kernel k_u in
                            if uu___3
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStarC_Syntax_Syntax.U_zero, FStarC_Syntax_Syntax.U_zero, [])
              us1 in
          match uu___ with
          | (uu___1, u1, out) -> FStarC_Compiler_List.rev (u1 :: out) in
        let rec aux u1 =
          let u2 = FStarC_Syntax_Subst.compress_univ u1 in
          match u2 with
          | FStarC_Syntax_Syntax.U_bvar x ->
              (try
                 (fun uu___ ->
                    match () with
                    | () ->
                        let uu___1 =
                          let uu___2 = FStarC_Compiler_List.nth env1 x in
                          FStar_Pervasives_Native.__proj__Mktuple3__item___2
                            uu___2 in
                        (match uu___1 with
                         | Univ u3 ->
                             ((let uu___3 =
                                 FStarC_Compiler_Effect.op_Bang dbg_univ_norm in
                               if uu___3
                               then
                                 let uu___4 =
                                   FStarC_Class_Show.show
                                     FStarC_Syntax_Print.showable_univ u3 in
                                 FStarC_Compiler_Util.print1
                                   "Univ (in norm_universe): %s\n" uu___4
                               else ());
                              aux u3)
                         | Dummy -> [u2]
                         | uu___2 ->
                             let uu___3 =
                               let uu___4 =
                                 FStarC_Compiler_Util.string_of_int x in
                               FStarC_Compiler_Util.format1
                                 "Impossible: universe variable u@%s bound to a term"
                                 uu___4 in
                             failwith uu___3)) ()
               with
               | uu___ ->
                   if
                     (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.allow_unbound_universes
                   then [FStarC_Syntax_Syntax.U_unknown]
                   else
                     (let uu___2 =
                        let uu___3 = FStarC_Compiler_Util.string_of_int x in
                        Prims.strcat "Universe variable not found: u@" uu___3 in
                      failwith uu___2))
          | FStarC_Syntax_Syntax.U_unif uu___ when
              (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.default_univs_to_zero
              -> [FStarC_Syntax_Syntax.U_zero]
          | FStarC_Syntax_Syntax.U_unif uu___ when
              (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.check_no_uvars
              ->
              let uu___1 =
                let uu___2 =
                  let uu___3 =
                    FStarC_TypeChecker_Env.get_range
                      cfg.FStarC_TypeChecker_Cfg.tcenv in
                  FStarC_Compiler_Range_Ops.string_of_range uu___3 in
                let uu___3 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ u2 in
                FStarC_Compiler_Util.format2
                  "(%s) CheckNoUvars: unexpected universes variable remains: %s"
                  uu___2 uu___3 in
              failwith uu___1
          | FStarC_Syntax_Syntax.U_zero -> [u2]
          | FStarC_Syntax_Syntax.U_unif uu___ -> [u2]
          | FStarC_Syntax_Syntax.U_name uu___ -> [u2]
          | FStarC_Syntax_Syntax.U_unknown -> [u2]
          | FStarC_Syntax_Syntax.U_max [] -> [FStarC_Syntax_Syntax.U_zero]
          | FStarC_Syntax_Syntax.U_max us ->
              let us1 =
                let uu___ = FStarC_Compiler_List.collect aux us in
                norm_univs_for_max uu___ in
              (match us1 with
               | u_k::hd::rest ->
                   let rest1 = hd :: rest in
                   let uu___ = FStarC_Syntax_Util.univ_kernel u_k in
                   (match uu___ with
                    | (FStarC_Syntax_Syntax.U_zero, n) ->
                        let uu___1 =
                          FStarC_Compiler_List.for_all
                            (fun u3 ->
                               let uu___2 = FStarC_Syntax_Util.univ_kernel u3 in
                               match uu___2 with | (uu___3, m) -> n <= m)
                            rest1 in
                        if uu___1 then rest1 else us1
                    | uu___1 -> us1)
               | uu___ -> us1)
          | FStarC_Syntax_Syntax.U_succ u3 ->
              let uu___ = aux u3 in
              FStarC_Compiler_List.map
                (fun uu___1 -> FStarC_Syntax_Syntax.U_succ uu___1) uu___ in
        if
          (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.erase_universes
        then FStarC_Syntax_Syntax.U_unknown
        else
          (let uu___1 = aux u in
           match uu___1 with
           | [] -> FStarC_Syntax_Syntax.U_zero
           | (FStarC_Syntax_Syntax.U_zero)::[] -> FStarC_Syntax_Syntax.U_zero
           | (FStarC_Syntax_Syntax.U_zero)::u1::[] -> u1
           | (FStarC_Syntax_Syntax.U_zero)::us ->
               FStarC_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStarC_Syntax_Syntax.U_max us)
let memo_or : 'a . 'a FStarC_Syntax_Syntax.memo -> (unit -> 'a) -> 'a =
  fun m ->
    fun f ->
      let uu___ = FStarC_Compiler_Effect.op_Bang m in
      match uu___ with
      | FStar_Pervasives_Native.Some v -> v
      | FStar_Pervasives_Native.None ->
          let v = f () in
          (FStarC_Compiler_Effect.op_Colon_Equals m
             (FStar_Pervasives_Native.Some v);
           v)
let rec (env_subst : env -> FStarC_Syntax_Syntax.subst_t) =
  fun env1 ->
    let compute uu___ =
      let uu___1 =
        FStarC_Compiler_List.fold_left
          (fun uu___2 ->
             fun uu___3 ->
               match (uu___2, uu___3) with
               | ((s, i), (uu___4, c, uu___5)) ->
                   (match c with
                    | Clos (e, t, memo, fix) ->
                        let es = env_subst e in
                        let t1 =
                          let uu___6 = FStarC_Syntax_Subst.subst es t in
                          FStarC_Syntax_Subst.compress uu___6 in
                        (((FStarC_Syntax_Syntax.DT (i, t1)) :: s),
                          (i + Prims.int_one))
                    | Univ u ->
                        (((FStarC_Syntax_Syntax.UN (i, u)) :: s),
                          (i + Prims.int_one))
                    | Dummy -> (s, (i + Prims.int_one))))
          ([], Prims.int_zero) env1 in
      match uu___1 with | (s, uu___2) -> s in
    match env1 with
    | [] -> []
    | (uu___, uu___1, memo)::uu___2 ->
        let uu___3 = FStarC_Compiler_Effect.op_Bang memo in
        (match uu___3 with
         | FStar_Pervasives_Native.Some s -> s
         | FStar_Pervasives_Native.None ->
             let s = compute () in
             (FStarC_Compiler_Effect.op_Colon_Equals memo
                (FStar_Pervasives_Native.Some s);
              s))
let (filter_out_lcomp_cflags :
  FStarC_Syntax_Syntax.cflag Prims.list ->
    FStarC_Syntax_Syntax.cflag Prims.list)
  =
  fun flags ->
    FStarC_Compiler_List.filter
      (fun uu___ ->
         match uu___ with
         | FStarC_Syntax_Syntax.DECREASES uu___1 -> false
         | uu___1 -> true) flags
let (default_univ_uvars_to_zero :
  FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) =
  fun t ->
    FStarC_Syntax_Visit.visit_term_univs false (fun t1 -> t1)
      (fun u ->
         match u with
         | FStarC_Syntax_Syntax.U_unif uu___ -> FStarC_Syntax_Syntax.U_zero
         | uu___ -> u) t
let (_erase_universes :
  FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) =
  fun t ->
    FStarC_Syntax_Visit.visit_term_univs false (fun t1 -> t1)
      (fun u -> FStarC_Syntax_Syntax.U_unknown) t
let (closure_as_term :
  FStarC_TypeChecker_Cfg.cfg ->
    env -> FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env1 ->
      fun t ->
        FStarC_TypeChecker_Cfg.log cfg
          (fun uu___1 ->
             let uu___2 =
               FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t in
             let uu___3 =
               FStarC_Class_Show.show
                 (FStarC_Class_Show.show_list
                    (FStarC_Class_Show.show_tuple3
                       (FStarC_Class_Show.show_option
                          FStarC_Syntax_Print.showable_binder)
                       showable_closure
                       (showable_memo
                          (FStarC_Class_Show.show_list
                             FStarC_Syntax_Print.showable_subst_elt)))) env1 in
             let uu___4 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
             FStarC_Compiler_Util.print3
               ">>> %s (env=%s)\nClosure_as_term %s\n" uu___2 uu___3 uu___4);
        (let es = env_subst env1 in
         let t1 = FStarC_Syntax_Subst.subst es t in
         let t2 =
           if
             (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.erase_universes
           then _erase_universes t1
           else
             if
               (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.default_univs_to_zero
             then default_univ_uvars_to_zero t1
             else t1 in
         let t3 = FStarC_Syntax_Subst.compress t2 in
         FStarC_TypeChecker_Cfg.log cfg
           (fun uu___2 ->
              let uu___3 =
                FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term
                  t3 in
              let uu___4 =
                FStarC_Class_Show.show
                  (FStarC_Class_Show.show_list
                     (FStarC_Class_Show.show_tuple3
                        (FStarC_Class_Show.show_option
                           FStarC_Syntax_Print.showable_binder)
                        showable_closure
                        (showable_memo
                           (FStarC_Class_Show.show_list
                              FStarC_Syntax_Print.showable_subst_elt)))) env1 in
              let uu___5 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t3 in
              FStarC_Compiler_Util.print3
                ">>> %s (env=%s)\nClosure_as_term RESULT %s\n" uu___3 uu___4
                uu___5);
         t3)
let (unembed_binder_knot :
  FStarC_Syntax_Syntax.binder FStarC_Syntax_Embeddings_Base.embedding
    FStar_Pervasives_Native.option FStarC_Compiler_Effect.ref)
  = FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None
let (unembed_binder :
  FStarC_Syntax_Syntax.term ->
    FStarC_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ = FStarC_Compiler_Effect.op_Bang unembed_binder_knot in
    match uu___ with
    | FStar_Pervasives_Native.Some e ->
        FStarC_Syntax_Embeddings_Base.try_unembed e t
          FStarC_Syntax_Embeddings_Base.id_norm_cb
    | FStar_Pervasives_Native.None ->
        (FStarC_Errors.log_issue (FStarC_Syntax_Syntax.has_range_syntax ()) t
           FStarC_Errors_Codes.Warning_UnembedBinderKnot ()
           (Obj.magic FStarC_Errors_Msg.is_error_message_string)
           (Obj.magic "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
let (mk_psc_subst :
  FStarC_TypeChecker_Cfg.cfg ->
    env -> FStarC_Syntax_Syntax.subst_elt Prims.list)
  =
  fun cfg ->
    fun env1 ->
      FStarC_Compiler_List.fold_right
        (fun uu___ ->
           fun subst ->
             match uu___ with
             | (binder_opt, closure1, uu___1) ->
                 (match (binder_opt, closure1) with
                  | (FStar_Pervasives_Native.Some b, Clos
                     (env2, term, uu___2, uu___3)) ->
                      let bv = b.FStarC_Syntax_Syntax.binder_bv in
                      let uu___4 =
                        let uu___5 =
                          FStarC_Syntax_Util.is_constructed_typ
                            bv.FStarC_Syntax_Syntax.sort
                            FStarC_Parser_Const.binder_lid in
                        Prims.op_Negation uu___5 in
                      if uu___4
                      then subst
                      else
                        (let term1 = closure_as_term cfg env2 term in
                         let uu___6 = unembed_binder term1 in
                         match uu___6 with
                         | FStar_Pervasives_Native.None -> subst
                         | FStar_Pervasives_Native.Some x ->
                             let b1 =
                               let uu___7 =
                                 let uu___8 =
                                   FStarC_Syntax_Subst.subst subst
                                     (x.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                 {
                                   FStarC_Syntax_Syntax.ppname =
                                     (bv.FStarC_Syntax_Syntax.ppname);
                                   FStarC_Syntax_Syntax.index =
                                     (bv.FStarC_Syntax_Syntax.index);
                                   FStarC_Syntax_Syntax.sort = uu___8
                                 } in
                               FStarC_Syntax_Syntax.freshen_bv uu___7 in
                             let b_for_x =
                               let uu___7 =
                                 let uu___8 =
                                   FStarC_Syntax_Syntax.bv_to_name b1 in
                                 ((x.FStarC_Syntax_Syntax.binder_bv), uu___8) in
                               FStarC_Syntax_Syntax.NT uu___7 in
                             let subst1 =
                               FStarC_Compiler_List.filter
                                 (fun uu___7 ->
                                    match uu___7 with
                                    | FStarC_Syntax_Syntax.NT
                                        (uu___8,
                                         {
                                           FStarC_Syntax_Syntax.n =
                                             FStarC_Syntax_Syntax.Tm_name b';
                                           FStarC_Syntax_Syntax.pos = uu___9;
                                           FStarC_Syntax_Syntax.vars =
                                             uu___10;
                                           FStarC_Syntax_Syntax.hash_code =
                                             uu___11;_})
                                        ->
                                        let uu___12 =
                                          FStarC_Ident.ident_equals
                                            b1.FStarC_Syntax_Syntax.ppname
                                            b'.FStarC_Syntax_Syntax.ppname in
                                        Prims.op_Negation uu___12
                                    | uu___8 -> true) subst in
                             b_for_x :: subst1)
                  | uu___2 -> subst)) env1 []
let (reduce_primops :
  FStarC_Syntax_Embeddings_Base.norm_cb ->
    FStarC_TypeChecker_Cfg.cfg ->
      env ->
        FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
          (FStarC_Syntax_Syntax.term * Prims.bool))
  =
  fun norm_cb ->
    fun cfg ->
      fun env1 ->
        fun tm ->
          if
            Prims.op_Negation
              (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.primops
          then (tm, false)
          else
            (let uu___1 = FStarC_Syntax_Util.head_and_args_full tm in
             match uu___1 with
             | (head, args) ->
                 let uu___2 =
                   let head1 =
                     let uu___3 = FStarC_Syntax_Util.unmeta head in
                     FStarC_Syntax_Subst.compress uu___3 in
                   match head1.FStarC_Syntax_Syntax.n with
                   | FStarC_Syntax_Syntax.Tm_uinst (fv, us) -> (fv, us)
                   | uu___3 -> (head1, []) in
                 (match uu___2 with
                  | (head_term, universes) ->
                      (match head_term.FStarC_Syntax_Syntax.n with
                       | FStarC_Syntax_Syntax.Tm_fvar fv ->
                           let uu___3 =
                             FStarC_TypeChecker_Cfg.find_prim_step cfg fv in
                           (match uu___3 with
                            | FStar_Pervasives_Native.Some prim_step when
                                prim_step.FStarC_TypeChecker_Primops_Base.strong_reduction_ok
                                  ||
                                  (Prims.op_Negation
                                     cfg.FStarC_TypeChecker_Cfg.strong)
                                ->
                                let l = FStarC_Compiler_List.length args in
                                if
                                  l <
                                    prim_step.FStarC_TypeChecker_Primops_Base.arity
                                then
                                  (FStarC_TypeChecker_Cfg.log_primops cfg
                                     (fun uu___5 ->
                                        let uu___6 =
                                          FStarC_Class_Show.show
                                            FStarC_Ident.showable_lident
                                            prim_step.FStarC_TypeChecker_Primops_Base.name in
                                        let uu___7 =
                                          FStarC_Class_Show.show
                                            FStarC_Class_Show.showable_nat l in
                                        let uu___8 =
                                          FStarC_Class_Show.show
                                            FStarC_Class_Show.showable_int
                                            prim_step.FStarC_TypeChecker_Primops_Base.arity in
                                        FStarC_Compiler_Util.print3
                                          "primop: found partially applied %s (%s/%s args)\n"
                                          uu___6 uu___7 uu___8);
                                   (tm, false))
                                else
                                  (let uu___5 =
                                     if
                                       l =
                                         prim_step.FStarC_TypeChecker_Primops_Base.arity
                                     then (args, [])
                                     else
                                       FStarC_Compiler_List.splitAt
                                         prim_step.FStarC_TypeChecker_Primops_Base.arity
                                         args in
                                   match uu___5 with
                                   | (args_1, args_2) ->
                                       (FStarC_TypeChecker_Cfg.log_primops
                                          cfg
                                          (fun uu___7 ->
                                             let uu___8 =
                                               FStarC_Class_Show.show
                                                 FStarC_Syntax_Print.showable_term
                                                 tm in
                                             FStarC_Compiler_Util.print1
                                               "primop: trying to reduce <%s>\n"
                                               uu___8);
                                        (let psc =
                                           {
                                             FStarC_TypeChecker_Primops_Base.psc_range
                                               =
                                               (head.FStarC_Syntax_Syntax.pos);
                                             FStarC_TypeChecker_Primops_Base.psc_subst
                                               =
                                               (fun uu___7 ->
                                                  if
                                                    prim_step.FStarC_TypeChecker_Primops_Base.requires_binder_substitution
                                                  then mk_psc_subst cfg env1
                                                  else [])
                                           } in
                                         let r =
                                           prim_step.FStarC_TypeChecker_Primops_Base.interpretation
                                             psc norm_cb universes args_1 in
                                         match r with
                                         | FStar_Pervasives_Native.None ->
                                             (FStarC_TypeChecker_Cfg.log_primops
                                                cfg
                                                (fun uu___8 ->
                                                   let uu___9 =
                                                     FStarC_Class_Show.show
                                                       FStarC_Syntax_Print.showable_term
                                                       tm in
                                                   FStarC_Compiler_Util.print1
                                                     "primop: <%s> did not reduce\n"
                                                     uu___9);
                                              (tm, false))
                                         | FStar_Pervasives_Native.Some
                                             reduced ->
                                             (FStarC_TypeChecker_Cfg.log_primops
                                                cfg
                                                (fun uu___8 ->
                                                   let uu___9 =
                                                     FStarC_Class_Show.show
                                                       FStarC_Syntax_Print.showable_term
                                                       tm in
                                                   let uu___10 =
                                                     FStarC_Class_Show.show
                                                       FStarC_Syntax_Print.showable_term
                                                       reduced in
                                                   FStarC_Compiler_Util.print2
                                                     "primop: <%s> reduced to  %s\n"
                                                     uu___9 uu___10);
                                              (let uu___8 =
                                                 FStarC_Syntax_Util.mk_app
                                                   reduced args_2 in
                                               (uu___8,
                                                 (prim_step.FStarC_TypeChecker_Primops_Base.renorm_after)))))))
                            | FStar_Pervasives_Native.Some uu___4 ->
                                (FStarC_TypeChecker_Cfg.log_primops cfg
                                   (fun uu___6 ->
                                      let uu___7 =
                                        FStarC_Class_Show.show
                                          FStarC_Syntax_Print.showable_term
                                          tm in
                                      FStarC_Compiler_Util.print1
                                        "primop: not reducing <%s> since we're doing strong reduction\n"
                                        uu___7);
                                 (tm, false))
                            | FStar_Pervasives_Native.None -> (tm, false))
                       | FStarC_Syntax_Syntax.Tm_constant
                           (FStarC_Const.Const_range_of) when
                           Prims.op_Negation
                             cfg.FStarC_TypeChecker_Cfg.strong
                           ->
                           (FStarC_TypeChecker_Cfg.log_primops cfg
                              (fun uu___4 ->
                                 let uu___5 =
                                   FStarC_Class_Show.show
                                     FStarC_Syntax_Print.showable_term tm in
                                 FStarC_Compiler_Util.print1
                                   "primop: reducing <%s>\n" uu___5);
                            (match args with
                             | (a1, uu___4)::[] ->
                                 let uu___5 =
                                   FStarC_TypeChecker_Primops_Base.embed_simple
                                     FStarC_Syntax_Embeddings.e_range
                                     a1.FStarC_Syntax_Syntax.pos
                                     tm.FStarC_Syntax_Syntax.pos in
                                 (uu___5, false)
                             | uu___4 -> (tm, false)))
                       | FStarC_Syntax_Syntax.Tm_constant
                           (FStarC_Const.Const_set_range_of) when
                           Prims.op_Negation
                             cfg.FStarC_TypeChecker_Cfg.strong
                           ->
                           (FStarC_TypeChecker_Cfg.log_primops cfg
                              (fun uu___4 ->
                                 let uu___5 =
                                   FStarC_Class_Show.show
                                     FStarC_Syntax_Print.showable_term tm in
                                 FStarC_Compiler_Util.print1
                                   "primop: reducing <%s>\n" uu___5);
                            (match args with
                             | (t, uu___4)::(r, uu___5)::[] ->
                                 let uu___6 =
                                   FStarC_TypeChecker_Primops_Base.try_unembed_simple
                                     FStarC_Syntax_Embeddings.e_range r in
                                 (match uu___6 with
                                  | FStar_Pervasives_Native.Some rng ->
                                      let uu___7 =
                                        FStarC_Syntax_Subst.set_use_range rng
                                          t in
                                      (uu___7, false)
                                  | FStar_Pervasives_Native.None ->
                                      (tm, false))
                             | uu___4 -> (tm, false)))
                       | uu___3 -> (tm, false))))
let (reduce_equality :
  FStarC_Syntax_Embeddings_Base.norm_cb ->
    FStarC_TypeChecker_Cfg.cfg ->
      env ->
        FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
          (FStarC_Syntax_Syntax.term * Prims.bool))
  =
  fun norm_cb ->
    fun cfg ->
      fun tm ->
        let uu___ =
          let uu___1 =
            FStarC_TypeChecker_Cfg.simplification_steps
              cfg.FStarC_TypeChecker_Cfg.tcenv in
          {
            FStarC_TypeChecker_Cfg.steps =
              {
                FStarC_TypeChecker_Cfg.beta =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.beta);
                FStarC_TypeChecker_Cfg.iota =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.iota);
                FStarC_TypeChecker_Cfg.zeta =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.zeta);
                FStarC_TypeChecker_Cfg.zeta_full =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.zeta_full);
                FStarC_TypeChecker_Cfg.weak =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.weak);
                FStarC_TypeChecker_Cfg.hnf =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.hnf);
                FStarC_TypeChecker_Cfg.primops = true;
                FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets);
                FStarC_TypeChecker_Cfg.unfold_until =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.unfold_until);
                FStarC_TypeChecker_Cfg.unfold_only =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.unfold_only);
                FStarC_TypeChecker_Cfg.unfold_fully =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.unfold_fully);
                FStarC_TypeChecker_Cfg.unfold_attr =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.unfold_attr);
                FStarC_TypeChecker_Cfg.unfold_qual =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.unfold_qual);
                FStarC_TypeChecker_Cfg.unfold_namespace =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.unfold_namespace);
                FStarC_TypeChecker_Cfg.dont_unfold_attr =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.dont_unfold_attr);
                FStarC_TypeChecker_Cfg.pure_subterms_within_computations =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.pure_subterms_within_computations);
                FStarC_TypeChecker_Cfg.simplify =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.simplify);
                FStarC_TypeChecker_Cfg.erase_universes =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.erase_universes);
                FStarC_TypeChecker_Cfg.allow_unbound_universes =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.allow_unbound_universes);
                FStarC_TypeChecker_Cfg.reify_ =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.reify_);
                FStarC_TypeChecker_Cfg.compress_uvars =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.compress_uvars);
                FStarC_TypeChecker_Cfg.no_full_norm =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.no_full_norm);
                FStarC_TypeChecker_Cfg.check_no_uvars =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.check_no_uvars);
                FStarC_TypeChecker_Cfg.unmeta =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.unmeta);
                FStarC_TypeChecker_Cfg.unascribe =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.unascribe);
                FStarC_TypeChecker_Cfg.in_full_norm_request =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.in_full_norm_request);
                FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee);
                FStarC_TypeChecker_Cfg.nbe_step =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.nbe_step);
                FStarC_TypeChecker_Cfg.for_extraction =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.for_extraction);
                FStarC_TypeChecker_Cfg.unrefine =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.unrefine);
                FStarC_TypeChecker_Cfg.default_univs_to_zero =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.default_univs_to_zero);
                FStarC_TypeChecker_Cfg.tactics =
                  (FStarC_TypeChecker_Cfg.default_steps.FStarC_TypeChecker_Cfg.tactics)
              };
            FStarC_TypeChecker_Cfg.tcenv = (cfg.FStarC_TypeChecker_Cfg.tcenv);
            FStarC_TypeChecker_Cfg.debug = (cfg.FStarC_TypeChecker_Cfg.debug);
            FStarC_TypeChecker_Cfg.delta_level =
              (cfg.FStarC_TypeChecker_Cfg.delta_level);
            FStarC_TypeChecker_Cfg.primitive_steps = uu___1;
            FStarC_TypeChecker_Cfg.strong =
              (cfg.FStarC_TypeChecker_Cfg.strong);
            FStarC_TypeChecker_Cfg.memoize_lazy =
              (cfg.FStarC_TypeChecker_Cfg.memoize_lazy);
            FStarC_TypeChecker_Cfg.normalize_pure_lets =
              (cfg.FStarC_TypeChecker_Cfg.normalize_pure_lets);
            FStarC_TypeChecker_Cfg.reifying =
              (cfg.FStarC_TypeChecker_Cfg.reifying);
            FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
              (cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
          } in
        reduce_primops norm_cb uu___ tm
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
  FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.args -> norm_request_t) =
  fun hd ->
    fun args ->
      let aux min_args =
        if (FStarC_Compiler_List.length args) < min_args
        then Norm_request_none
        else
          if (FStarC_Compiler_List.length args) = min_args
          then Norm_request_ready
          else Norm_request_requires_rejig in
      let uu___ =
        let uu___1 = FStarC_Syntax_Util.un_uinst hd in
        uu___1.FStarC_Syntax_Syntax.n in
      match uu___ with
      | FStarC_Syntax_Syntax.Tm_fvar fv when
          FStarC_Syntax_Syntax.fv_eq_lid fv
            FStarC_Parser_Const.normalize_term
          -> aux (Prims.of_int (2))
      | FStarC_Syntax_Syntax.Tm_fvar fv when
          FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.normalize ->
          aux Prims.int_one
      | FStarC_Syntax_Syntax.Tm_fvar fv when
          FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.norm ->
          aux (Prims.of_int (3))
      | uu___1 -> Norm_request_none
let (should_consider_norm_requests :
  FStarC_TypeChecker_Cfg.cfg -> Prims.bool) =
  fun cfg ->
    (Prims.op_Negation
       (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.no_full_norm)
      &&
      (let uu___ =
         FStarC_Ident.lid_equals
           (cfg.FStarC_TypeChecker_Cfg.tcenv).FStarC_TypeChecker_Env.curmodule
           FStarC_Parser_Const.prims_lid in
       Prims.op_Negation uu___)
let (rejig_norm_request :
  FStarC_Syntax_Syntax.term ->
    FStarC_Syntax_Syntax.args -> FStarC_Syntax_Syntax.term)
  =
  fun hd ->
    fun args ->
      let uu___ =
        let uu___1 = FStarC_Syntax_Util.un_uinst hd in
        uu___1.FStarC_Syntax_Syntax.n in
      match uu___ with
      | FStarC_Syntax_Syntax.Tm_fvar fv when
          FStarC_Syntax_Syntax.fv_eq_lid fv
            FStarC_Parser_Const.normalize_term
          ->
          (match args with
           | t1::t2::rest when
               (FStarC_Compiler_List.length rest) > Prims.int_zero ->
               let uu___1 = FStarC_Syntax_Util.mk_app hd [t1; t2] in
               FStarC_Syntax_Util.mk_app uu___1 rest
           | uu___1 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize_term")
      | FStarC_Syntax_Syntax.Tm_fvar fv when
          FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.normalize ->
          (match args with
           | t::rest when (FStarC_Compiler_List.length rest) > Prims.int_zero
               ->
               let uu___1 = FStarC_Syntax_Util.mk_app hd [t] in
               FStarC_Syntax_Util.mk_app uu___1 rest
           | uu___1 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize")
      | FStarC_Syntax_Syntax.Tm_fvar fv when
          FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.norm ->
          (match args with
           | t1::t2::t3::rest when
               (FStarC_Compiler_List.length rest) > Prims.int_zero ->
               let uu___1 = FStarC_Syntax_Util.mk_app hd [t1; t2; t3] in
               FStarC_Syntax_Util.mk_app uu___1 rest
           | uu___1 ->
               failwith "Impossible! invalid rejig_norm_request for norm")
      | uu___1 ->
          let uu___2 =
            let uu___3 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term hd in
            Prims.strcat "Impossible! invalid rejig_norm_request for: %s"
              uu___3 in
          failwith uu___2
let (is_nbe_request : FStarC_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s ->
    FStarC_Compiler_Util.for_some
      (FStarC_Class_Deq.op_Equals_Question FStarC_TypeChecker_Env.deq_step
         FStarC_TypeChecker_Env.NBE) s
let get_norm_request :
  'uuuuu .
    FStarC_TypeChecker_Cfg.cfg ->
      (FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) ->
        (FStarC_Syntax_Syntax.term * 'uuuuu) Prims.list ->
          (FStarC_TypeChecker_Env.step Prims.list *
            FStarC_Syntax_Syntax.term) FStar_Pervasives_Native.option
  =
  fun cfg ->
    fun full_norm ->
      fun args ->
        let parse_steps s =
          let uu___ =
            FStarC_TypeChecker_Primops_Base.try_unembed_simple
              (FStarC_Syntax_Embeddings.e_list
                 FStarC_Syntax_Embeddings.e_norm_step) s in
          match uu___ with
          | FStar_Pervasives_Native.Some steps ->
              let uu___1 = FStarC_TypeChecker_Cfg.translate_norm_steps steps in
              FStar_Pervasives_Native.Some uu___1
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None in
        let inherited_steps =
          FStarC_Compiler_List.op_At
            (if
               (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.erase_universes
             then [FStarC_TypeChecker_Env.EraseUniverses]
             else [])
            (FStarC_Compiler_List.op_At
               (if
                  (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.allow_unbound_universes
                then [FStarC_TypeChecker_Env.AllowUnboundUniverses]
                else [])
               (if
                  (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.nbe_step
                then [FStarC_TypeChecker_Env.NBE]
                else [])) in
        match args with
        | uu___::(tm, uu___1)::[] ->
            let s =
              [FStarC_TypeChecker_Env.Beta;
              FStarC_TypeChecker_Env.Zeta;
              FStarC_TypeChecker_Env.Iota;
              FStarC_TypeChecker_Env.Primops;
              FStarC_TypeChecker_Env.UnfoldUntil
                FStarC_Syntax_Syntax.delta_constant;
              FStarC_TypeChecker_Env.Reify] in
            FStar_Pervasives_Native.Some
              ((FStarC_Compiler_List.op_At
                  ((FStarC_TypeChecker_Env.DontUnfoldAttr
                      [FStarC_Parser_Const.tac_opaque_attr]) ::
                  inherited_steps) s), tm)
        | (tm, uu___)::[] ->
            let s =
              [FStarC_TypeChecker_Env.Beta;
              FStarC_TypeChecker_Env.Zeta;
              FStarC_TypeChecker_Env.Iota;
              FStarC_TypeChecker_Env.Primops;
              FStarC_TypeChecker_Env.UnfoldUntil
                FStarC_Syntax_Syntax.delta_constant;
              FStarC_TypeChecker_Env.Reify] in
            FStar_Pervasives_Native.Some
              ((FStarC_Compiler_List.op_At
                  ((FStarC_TypeChecker_Env.DontUnfoldAttr
                      [FStarC_Parser_Const.tac_opaque_attr]) ::
                  inherited_steps) s), tm)
        | (steps, uu___)::uu___1::(tm, uu___2)::[] ->
            let uu___3 = let uu___4 = full_norm steps in parse_steps uu___4 in
            (match uu___3 with
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 FStar_Pervasives_Native.Some
                   ((FStarC_Compiler_List.op_At
                       ((FStarC_TypeChecker_Env.DontUnfoldAttr
                           [FStarC_Parser_Const.tac_opaque_attr]) ::
                       inherited_steps) s), tm))
        | uu___ -> FStar_Pervasives_Native.None
let (nbe_eval :
  FStarC_TypeChecker_Cfg.cfg ->
    FStarC_TypeChecker_Env.steps ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun cfg ->
    fun s ->
      fun tm ->
        let delta_level =
          let uu___ =
            FStarC_Compiler_Util.for_some
              (fun uu___1 ->
                 match uu___1 with
                 | FStarC_TypeChecker_Env.UnfoldUntil uu___2 -> true
                 | FStarC_TypeChecker_Env.UnfoldOnly uu___2 -> true
                 | FStarC_TypeChecker_Env.UnfoldFully uu___2 -> true
                 | uu___2 -> false) s in
          if uu___
          then
            [FStarC_TypeChecker_Env.Unfold
               FStarC_Syntax_Syntax.delta_constant]
          else [FStarC_TypeChecker_Env.NoDelta] in
        FStarC_TypeChecker_Cfg.log_nbe cfg
          (fun uu___1 ->
             let uu___2 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term tm in
             FStarC_Compiler_Util.print1 "Invoking NBE with  %s\n" uu___2);
        (let tm_norm =
           let uu___1 = FStarC_TypeChecker_Cfg.cfg_env cfg in
           uu___1.FStarC_TypeChecker_Env.nbe s
             cfg.FStarC_TypeChecker_Cfg.tcenv tm in
         FStarC_TypeChecker_Cfg.log_nbe cfg
           (fun uu___2 ->
              let uu___3 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                  tm_norm in
              FStarC_Compiler_Util.print1 "Result of NBE is  %s\n" uu___3);
         tm_norm)
let firstn :
  'uuuuu .
    Prims.int -> 'uuuuu Prims.list -> ('uuuuu Prims.list * 'uuuuu Prims.list)
  =
  fun k ->
    fun l ->
      if (FStarC_Compiler_List.length l) < k
      then (l, [])
      else FStarC_Compiler_Util.first_N k l
let (should_reify :
  FStarC_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
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
             FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_constant
               (FStarC_Const.Const_reify uu___2);
             FStarC_Syntax_Syntax.pos = uu___3;
             FStarC_Syntax_Syntax.vars = uu___4;
             FStarC_Syntax_Syntax.hash_code = uu___5;_},
           uu___6, uu___7))::uu___8
          -> (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.reify_
      | uu___1 -> false
let rec (maybe_weakly_reduced :
  FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm ->
    let aux_comp c =
      match c.FStarC_Syntax_Syntax.n with
      | FStarC_Syntax_Syntax.GTotal t -> maybe_weakly_reduced t
      | FStarC_Syntax_Syntax.Total t -> maybe_weakly_reduced t
      | FStarC_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStarC_Syntax_Syntax.result_typ) ||
            (FStarC_Compiler_Util.for_some
               (fun uu___ ->
                  match uu___ with | (a, uu___1) -> maybe_weakly_reduced a)
               ct.FStarC_Syntax_Syntax.effect_args) in
    let t = FStarC_Syntax_Subst.compress tm in
    match t.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Tm_delayed uu___ -> failwith "Impossible"
    | FStarC_Syntax_Syntax.Tm_name uu___ -> false
    | FStarC_Syntax_Syntax.Tm_uvar uu___ -> false
    | FStarC_Syntax_Syntax.Tm_type uu___ -> false
    | FStarC_Syntax_Syntax.Tm_bvar uu___ -> false
    | FStarC_Syntax_Syntax.Tm_fvar uu___ -> false
    | FStarC_Syntax_Syntax.Tm_constant uu___ -> false
    | FStarC_Syntax_Syntax.Tm_lazy uu___ -> false
    | FStarC_Syntax_Syntax.Tm_unknown -> false
    | FStarC_Syntax_Syntax.Tm_uinst uu___ -> false
    | FStarC_Syntax_Syntax.Tm_quoted uu___ -> false
    | FStarC_Syntax_Syntax.Tm_let uu___ -> true
    | FStarC_Syntax_Syntax.Tm_abs uu___ -> true
    | FStarC_Syntax_Syntax.Tm_arrow uu___ -> true
    | FStarC_Syntax_Syntax.Tm_refine uu___ -> true
    | FStarC_Syntax_Syntax.Tm_match uu___ -> true
    | FStarC_Syntax_Syntax.Tm_app
        { FStarC_Syntax_Syntax.hd = t1; FStarC_Syntax_Syntax.args = args;_}
        ->
        (maybe_weakly_reduced t1) ||
          (FStarC_Compiler_Util.for_some
             (fun uu___ ->
                match uu___ with | (a, uu___1) -> maybe_weakly_reduced a)
             args)
    | FStarC_Syntax_Syntax.Tm_ascribed
        { FStarC_Syntax_Syntax.tm = t1; FStarC_Syntax_Syntax.asc = asc;
          FStarC_Syntax_Syntax.eff_opt = uu___;_}
        ->
        (maybe_weakly_reduced t1) ||
          (let uu___1 = asc in
           (match uu___1 with
            | (asc_tc, asc_tac, uu___2) ->
                (match asc_tc with
                 | FStar_Pervasives.Inl t2 -> maybe_weakly_reduced t2
                 | FStar_Pervasives.Inr c2 -> aux_comp c2) ||
                  ((match asc_tac with
                    | FStar_Pervasives_Native.None -> false
                    | FStar_Pervasives_Native.Some tac ->
                        maybe_weakly_reduced tac))))
    | FStarC_Syntax_Syntax.Tm_meta
        { FStarC_Syntax_Syntax.tm2 = t1; FStarC_Syntax_Syntax.meta = m;_} ->
        (maybe_weakly_reduced t1) ||
          ((match m with
            | FStarC_Syntax_Syntax.Meta_pattern (uu___, args) ->
                FStarC_Compiler_Util.for_some
                  (FStarC_Compiler_Util.for_some
                     (fun uu___1 ->
                        match uu___1 with
                        | (a, uu___2) -> maybe_weakly_reduced a)) args
            | FStarC_Syntax_Syntax.Meta_monadic_lift (uu___, uu___1, t') ->
                maybe_weakly_reduced t'
            | FStarC_Syntax_Syntax.Meta_monadic (uu___, t') ->
                maybe_weakly_reduced t'
            | FStarC_Syntax_Syntax.Meta_labeled uu___ -> false
            | FStarC_Syntax_Syntax.Meta_desugared uu___ -> false
            | FStarC_Syntax_Syntax.Meta_named uu___ -> false))
let (decide_unfolding :
  FStarC_TypeChecker_Cfg.cfg ->
    stack_elt Prims.list ->
      FStarC_Syntax_Syntax.fv ->
        FStarC_TypeChecker_Env.qninfo ->
          (FStarC_TypeChecker_Cfg.cfg FStar_Pervasives_Native.option *
            stack_elt Prims.list) FStar_Pervasives_Native.option)
  =
  fun cfg ->
    fun stack1 ->
      fun fv ->
        fun qninfo ->
          let res =
            FStarC_TypeChecker_Normalize_Unfolding.should_unfold cfg
              (fun cfg1 -> should_reify cfg1 stack1) fv qninfo in
          match res with
          | FStarC_TypeChecker_Normalize_Unfolding.Should_unfold_no ->
              FStar_Pervasives_Native.None
          | FStarC_TypeChecker_Normalize_Unfolding.Should_unfold_yes ->
              FStar_Pervasives_Native.Some
                (FStar_Pervasives_Native.None, stack1)
          | FStarC_TypeChecker_Normalize_Unfolding.Should_unfold_fully ->
              let cfg' =
                {
                  FStarC_TypeChecker_Cfg.steps =
                    (let uu___ = cfg.FStarC_TypeChecker_Cfg.steps in
                     {
                       FStarC_TypeChecker_Cfg.beta =
                         (uu___.FStarC_TypeChecker_Cfg.beta);
                       FStarC_TypeChecker_Cfg.iota =
                         (uu___.FStarC_TypeChecker_Cfg.iota);
                       FStarC_TypeChecker_Cfg.zeta =
                         (uu___.FStarC_TypeChecker_Cfg.zeta);
                       FStarC_TypeChecker_Cfg.zeta_full =
                         (uu___.FStarC_TypeChecker_Cfg.zeta_full);
                       FStarC_TypeChecker_Cfg.weak =
                         (uu___.FStarC_TypeChecker_Cfg.weak);
                       FStarC_TypeChecker_Cfg.hnf =
                         (uu___.FStarC_TypeChecker_Cfg.hnf);
                       FStarC_TypeChecker_Cfg.primops =
                         (uu___.FStarC_TypeChecker_Cfg.primops);
                       FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets =
                         (uu___.FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets);
                       FStarC_TypeChecker_Cfg.unfold_until =
                         (FStar_Pervasives_Native.Some
                            FStarC_Syntax_Syntax.delta_constant);
                       FStarC_TypeChecker_Cfg.unfold_only =
                         FStar_Pervasives_Native.None;
                       FStarC_TypeChecker_Cfg.unfold_fully =
                         FStar_Pervasives_Native.None;
                       FStarC_TypeChecker_Cfg.unfold_attr =
                         FStar_Pervasives_Native.None;
                       FStarC_TypeChecker_Cfg.unfold_qual =
                         FStar_Pervasives_Native.None;
                       FStarC_TypeChecker_Cfg.unfold_namespace =
                         FStar_Pervasives_Native.None;
                       FStarC_TypeChecker_Cfg.dont_unfold_attr =
                         (uu___.FStarC_TypeChecker_Cfg.dont_unfold_attr);
                       FStarC_TypeChecker_Cfg.pure_subterms_within_computations
                         =
                         (uu___.FStarC_TypeChecker_Cfg.pure_subterms_within_computations);
                       FStarC_TypeChecker_Cfg.simplify =
                         (uu___.FStarC_TypeChecker_Cfg.simplify);
                       FStarC_TypeChecker_Cfg.erase_universes =
                         (uu___.FStarC_TypeChecker_Cfg.erase_universes);
                       FStarC_TypeChecker_Cfg.allow_unbound_universes =
                         (uu___.FStarC_TypeChecker_Cfg.allow_unbound_universes);
                       FStarC_TypeChecker_Cfg.reify_ =
                         (uu___.FStarC_TypeChecker_Cfg.reify_);
                       FStarC_TypeChecker_Cfg.compress_uvars =
                         (uu___.FStarC_TypeChecker_Cfg.compress_uvars);
                       FStarC_TypeChecker_Cfg.no_full_norm =
                         (uu___.FStarC_TypeChecker_Cfg.no_full_norm);
                       FStarC_TypeChecker_Cfg.check_no_uvars =
                         (uu___.FStarC_TypeChecker_Cfg.check_no_uvars);
                       FStarC_TypeChecker_Cfg.unmeta =
                         (uu___.FStarC_TypeChecker_Cfg.unmeta);
                       FStarC_TypeChecker_Cfg.unascribe =
                         (uu___.FStarC_TypeChecker_Cfg.unascribe);
                       FStarC_TypeChecker_Cfg.in_full_norm_request =
                         (uu___.FStarC_TypeChecker_Cfg.in_full_norm_request);
                       FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee =
                         (uu___.FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee);
                       FStarC_TypeChecker_Cfg.nbe_step =
                         (uu___.FStarC_TypeChecker_Cfg.nbe_step);
                       FStarC_TypeChecker_Cfg.for_extraction =
                         (uu___.FStarC_TypeChecker_Cfg.for_extraction);
                       FStarC_TypeChecker_Cfg.unrefine =
                         (uu___.FStarC_TypeChecker_Cfg.unrefine);
                       FStarC_TypeChecker_Cfg.default_univs_to_zero =
                         (uu___.FStarC_TypeChecker_Cfg.default_univs_to_zero);
                       FStarC_TypeChecker_Cfg.tactics =
                         (uu___.FStarC_TypeChecker_Cfg.tactics)
                     });
                  FStarC_TypeChecker_Cfg.tcenv =
                    (cfg.FStarC_TypeChecker_Cfg.tcenv);
                  FStarC_TypeChecker_Cfg.debug =
                    (cfg.FStarC_TypeChecker_Cfg.debug);
                  FStarC_TypeChecker_Cfg.delta_level =
                    (cfg.FStarC_TypeChecker_Cfg.delta_level);
                  FStarC_TypeChecker_Cfg.primitive_steps =
                    (cfg.FStarC_TypeChecker_Cfg.primitive_steps);
                  FStarC_TypeChecker_Cfg.strong =
                    (cfg.FStarC_TypeChecker_Cfg.strong);
                  FStarC_TypeChecker_Cfg.memoize_lazy =
                    (cfg.FStarC_TypeChecker_Cfg.memoize_lazy);
                  FStarC_TypeChecker_Cfg.normalize_pure_lets =
                    (cfg.FStarC_TypeChecker_Cfg.normalize_pure_lets);
                  FStarC_TypeChecker_Cfg.reifying =
                    (cfg.FStarC_TypeChecker_Cfg.reifying);
                  FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
                    (cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
                } in
              FStar_Pervasives_Native.Some
                ((FStar_Pervasives_Native.Some cfg'), stack1)
          | FStarC_TypeChecker_Normalize_Unfolding.Should_unfold_reify ->
              let rec push e s =
                match s with
                | [] -> [e]
                | (UnivArgs (us, r))::t ->
                    let uu___ = push e t in (UnivArgs (us, r)) :: uu___
                | h::t -> e :: h :: t in
              let ref =
                let uu___ =
                  let uu___1 =
                    let uu___2 = FStarC_Syntax_Syntax.lid_of_fv fv in
                    FStarC_Const.Const_reflect uu___2 in
                  FStarC_Syntax_Syntax.Tm_constant uu___1 in
                FStarC_Syntax_Syntax.mk uu___
                  FStarC_Compiler_Range_Type.dummyRange in
              let stack2 =
                push
                  (App
                     (empty_env, ref, FStar_Pervasives_Native.None,
                       FStarC_Compiler_Range_Type.dummyRange)) stack1 in
              FStar_Pervasives_Native.Some
                (FStar_Pervasives_Native.None, stack2)
let (on_domain_lids : FStarC_Ident.lident Prims.list) =
  [FStarC_Parser_Const.fext_on_domain_lid;
  FStarC_Parser_Const.fext_on_dom_lid;
  FStarC_Parser_Const.fext_on_domain_g_lid;
  FStarC_Parser_Const.fext_on_dom_g_lid]
let (is_fext_on_domain :
  FStarC_Syntax_Syntax.term ->
    FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t ->
    let is_on_dom fv =
      FStarC_Compiler_List.existsb
        (fun l -> FStarC_Syntax_Syntax.fv_eq_lid fv l) on_domain_lids in
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_app
        { FStarC_Syntax_Syntax.hd = hd; FStarC_Syntax_Syntax.args = args;_}
        ->
        let uu___1 =
          let uu___2 = FStarC_Syntax_Util.un_uinst hd in
          uu___2.FStarC_Syntax_Syntax.n in
        (match uu___1 with
         | FStarC_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStarC_Compiler_List.length args) = (Prims.of_int (3)))
             ->
             let f =
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStarC_Compiler_List.tl args in
                   FStarC_Compiler_List.tl uu___4 in
                 FStarC_Compiler_List.hd uu___3 in
               FStar_Pervasives_Native.fst uu___2 in
             FStar_Pervasives_Native.Some f
         | uu___2 -> FStar_Pervasives_Native.None)
    | uu___1 -> FStar_Pervasives_Native.None
let (__get_n_binders :
  (FStarC_TypeChecker_Env.env ->
     FStarC_TypeChecker_Env.step Prims.list ->
       Prims.int ->
         FStarC_Syntax_Syntax.term ->
           (FStarC_Syntax_Syntax.binder Prims.list *
             FStarC_Syntax_Syntax.comp))
    FStarC_Compiler_Effect.ref)
  =
  FStarC_Compiler_Util.mk_ref
    (fun e ->
       fun s ->
         fun n -> fun t -> failwith "Impossible: __get_n_binders unset")
let (is_partial_primop_app :
  FStarC_TypeChecker_Cfg.cfg -> FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun cfg ->
    fun t ->
      let uu___ = FStarC_Syntax_Util.head_and_args t in
      match uu___ with
      | (hd, args) ->
          let uu___1 =
            let uu___2 = FStarC_Syntax_Util.un_uinst hd in
            uu___2.FStarC_Syntax_Syntax.n in
          (match uu___1 with
           | FStarC_Syntax_Syntax.Tm_fvar fv ->
               let uu___2 = FStarC_TypeChecker_Cfg.find_prim_step cfg fv in
               (match uu___2 with
                | FStar_Pervasives_Native.Some prim_step ->
                    prim_step.FStarC_TypeChecker_Primops_Base.arity >
                      (FStarC_Compiler_List.length args)
                | FStar_Pervasives_Native.None -> false)
           | uu___2 -> false)
let (maybe_drop_rc_typ :
  FStarC_TypeChecker_Cfg.cfg ->
    FStarC_Syntax_Syntax.residual_comp -> FStarC_Syntax_Syntax.residual_comp)
  =
  fun cfg ->
    fun rc ->
      if
        (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
      then
        {
          FStarC_Syntax_Syntax.residual_effect =
            (rc.FStarC_Syntax_Syntax.residual_effect);
          FStarC_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.None;
          FStarC_Syntax_Syntax.residual_flags =
            (rc.FStarC_Syntax_Syntax.residual_flags)
        }
      else rc
let (get_extraction_mode :
  FStarC_TypeChecker_Env.env ->
    FStarC_Ident.lident -> FStarC_Syntax_Syntax.eff_extraction_mode)
  =
  fun env1 ->
    fun m ->
      let norm_m = FStarC_TypeChecker_Env.norm_eff_name env1 m in
      let uu___ = FStarC_TypeChecker_Env.get_effect_decl env1 norm_m in
      uu___.FStarC_Syntax_Syntax.extraction_mode
let (can_reify_for_extraction :
  FStarC_TypeChecker_Env.env -> FStarC_Ident.lident -> Prims.bool) =
  fun env1 ->
    fun m ->
      let uu___ = get_extraction_mode env1 m in
      uu___ = FStarC_Syntax_Syntax.Extract_reify
let rec args_are_binders :
  'uuuuu .
    (FStarC_Syntax_Syntax.term * 'uuuuu) Prims.list ->
      FStarC_Syntax_Syntax.binder Prims.list -> Prims.bool
  =
  fun args ->
    fun bs ->
      match (args, bs) with
      | ((t, uu___)::args1, b::bs1) ->
          let uu___1 =
            let uu___2 = FStarC_Syntax_Subst.compress t in
            uu___2.FStarC_Syntax_Syntax.n in
          (match uu___1 with
           | FStarC_Syntax_Syntax.Tm_name bv' ->
               (FStarC_Syntax_Syntax.bv_eq b.FStarC_Syntax_Syntax.binder_bv
                  bv')
                 && (args_are_binders args1 bs1)
           | uu___2 -> false)
      | ([], []) -> true
      | (uu___, uu___1) -> false
let (is_applied :
  FStarC_TypeChecker_Cfg.cfg ->
    FStarC_Syntax_Syntax.binders ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun cfg ->
    fun bs ->
      fun t ->
        if (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.wpe
        then
          (let uu___1 =
             FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
           let uu___2 =
             FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t in
           FStarC_Compiler_Util.print2 "WPE> is_applied %s -- %s\n" uu___1
             uu___2)
        else ();
        (let uu___1 = FStarC_Syntax_Util.head_and_args_full t in
         match uu___1 with
         | (hd, args) ->
             let uu___2 =
               let uu___3 = FStarC_Syntax_Subst.compress hd in
               uu___3.FStarC_Syntax_Syntax.n in
             (match uu___2 with
              | FStarC_Syntax_Syntax.Tm_name bv when args_are_binders args bs
                  ->
                  (if
                     (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.wpe
                   then
                     (let uu___4 =
                        FStarC_Class_Show.show
                          FStarC_Syntax_Print.showable_term t in
                      let uu___5 =
                        FStarC_Class_Show.show
                          FStarC_Syntax_Print.showable_bv bv in
                      let uu___6 =
                        FStarC_Class_Show.show
                          FStarC_Syntax_Print.showable_term hd in
                      FStarC_Compiler_Util.print3
                        "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                        uu___4 uu___5 uu___6)
                   else ();
                   FStar_Pervasives_Native.Some bv)
              | uu___3 -> FStar_Pervasives_Native.None))
let (is_applied_maybe_squashed :
  FStarC_TypeChecker_Cfg.cfg ->
    FStarC_Syntax_Syntax.binders ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun cfg ->
    fun bs ->
      fun t ->
        if (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.wpe
        then
          (let uu___1 =
             FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
           let uu___2 =
             FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t in
           FStarC_Compiler_Util.print2
             "WPE> is_applied_maybe_squashed %s -- %s\n" uu___1 uu___2)
        else ();
        (let uu___1 = FStarC_Syntax_Util.is_squash t in
         match uu___1 with
         | FStar_Pervasives_Native.Some (uu___2, t') -> is_applied cfg bs t'
         | uu___2 ->
             let uu___3 = FStarC_Syntax_Util.is_auto_squash t in
             (match uu___3 with
              | FStar_Pervasives_Native.Some (uu___4, t') ->
                  is_applied cfg bs t'
              | uu___4 -> is_applied cfg bs t))
let (is_quantified_const :
  FStarC_TypeChecker_Cfg.cfg ->
    FStarC_Syntax_Syntax.bv ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun cfg ->
           fun bv ->
             fun phi ->
               let guard b =
                 if b
                 then FStar_Pervasives_Native.Some ()
                 else FStar_Pervasives_Native.None in
               let phi0 = phi in
               let types_match bs =
                 let uu___ =
                   let uu___1 =
                     FStarC_Compiler_Effect.op_Bang __get_n_binders in
                   uu___1 cfg.FStarC_TypeChecker_Cfg.tcenv
                     [FStarC_TypeChecker_Env.AllowUnboundUniverses]
                     (FStarC_Compiler_List.length bs)
                     bv.FStarC_Syntax_Syntax.sort in
                 match uu___ with
                 | (bs_q, uu___1) ->
                     let rec unrefine_true t =
                       let uu___2 =
                         let uu___3 = FStarC_Syntax_Subst.compress t in
                         uu___3.FStarC_Syntax_Syntax.n in
                       match uu___2 with
                       | FStarC_Syntax_Syntax.Tm_refine
                           { FStarC_Syntax_Syntax.b = b;
                             FStarC_Syntax_Syntax.phi = phi1;_}
                           when
                           FStarC_Syntax_Util.term_eq phi1
                             FStarC_Syntax_Util.t_true
                           -> unrefine_true b.FStarC_Syntax_Syntax.sort
                       | uu___3 -> t in
                     ((FStarC_Compiler_List.length bs) =
                        (FStarC_Compiler_List.length bs_q))
                       &&
                       (FStarC_Compiler_List.forall2
                          (fun b1 ->
                             fun b2 ->
                               let s1 =
                                 unrefine_true
                                   (b1.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                               let s2 =
                                 unrefine_true
                                   (b2.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                               FStarC_Syntax_Util.term_eq s1 s2) bs bs_q) in
               let is_bv bv1 t =
                 let uu___ =
                   let uu___1 = FStarC_Syntax_Subst.compress t in
                   uu___1.FStarC_Syntax_Syntax.n in
                 match uu___ with
                 | FStarC_Syntax_Syntax.Tm_name bv' ->
                     FStarC_Syntax_Syntax.bv_eq bv1 bv'
                 | uu___1 -> false in
               let replace_full_applications_with bv1 arity s t =
                 let chgd = FStarC_Compiler_Util.mk_ref false in
                 let t' =
                   FStarC_Syntax_Visit.visit_term false
                     (fun t1 ->
                        let uu___ = FStarC_Syntax_Util.head_and_args t1 in
                        match uu___ with
                        | (hd, args) ->
                            let uu___1 =
                              ((FStarC_Compiler_List.length args) = arity) &&
                                (is_bv bv1 hd) in
                            if uu___1
                            then
                              (FStarC_Compiler_Effect.op_Colon_Equals chgd
                                 true;
                               s)
                            else t1) t in
                 let uu___ = FStarC_Compiler_Effect.op_Bang chgd in
                 (t', uu___) in
               let uu___ = FStarC_Syntax_Formula.destruct_typ_as_formula phi in
               Obj.magic
                 (FStarC_Class_Monad.op_let_Bang
                    FStarC_Class_Monad.monad_option () () (Obj.magic uu___)
                    (fun uu___1 ->
                       (fun form ->
                          let form = Obj.magic form in
                          match form with
                          | FStarC_Syntax_Formula.BaseConn
                              (lid, (p, uu___1)::(q, uu___2)::[]) when
                              FStarC_Ident.lid_equals lid
                                FStarC_Parser_Const.imp_lid
                              ->
                              Obj.magic
                                (Obj.repr
                                   (if
                                      (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.wpe
                                    then
                                      (let uu___4 =
                                         FStarC_Class_Show.show
                                           FStarC_Syntax_Print.showable_term
                                           p in
                                       let uu___5 =
                                         FStarC_Class_Show.show
                                           FStarC_Syntax_Print.showable_term
                                           q in
                                       FStarC_Compiler_Util.print2
                                         "WPE> p = (%s); q = (%s)\n" uu___4
                                         uu___5)
                                    else ();
                                    (let uu___4 =
                                       let uu___5 =
                                         FStarC_Syntax_Formula.destruct_typ_as_formula
                                           p in
                                       match uu___5 with
                                       | FStar_Pervasives_Native.None ->
                                           Obj.magic
                                             (Obj.repr
                                                (let uu___6 =
                                                   let uu___7 =
                                                     FStarC_Syntax_Subst.compress
                                                       p in
                                                   uu___7.FStarC_Syntax_Syntax.n in
                                                 match uu___6 with
                                                 | FStarC_Syntax_Syntax.Tm_bvar
                                                     bv' when
                                                     FStarC_Syntax_Syntax.bv_eq
                                                       bv bv'
                                                     ->
                                                     (if
                                                        (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.wpe
                                                      then
                                                        FStarC_Compiler_Util.print_string
                                                          "WPE> Case 1\n"
                                                      else ();
                                                      (let q' =
                                                         FStarC_Syntax_Subst.subst
                                                           [FStarC_Syntax_Syntax.NT
                                                              (bv,
                                                                FStarC_Syntax_Util.t_true)]
                                                           q in
                                                       FStar_Pervasives_Native.Some
                                                         q'))
                                                 | uu___7 ->
                                                     FStar_Pervasives_Native.None))
                                       | FStar_Pervasives_Native.Some
                                           (FStarC_Syntax_Formula.BaseConn
                                           (lid1, (p1, uu___6)::[])) when
                                           FStarC_Ident.lid_equals lid1
                                             FStarC_Parser_Const.not_lid
                                           ->
                                           Obj.magic
                                             (Obj.repr
                                                (let uu___7 =
                                                   let uu___8 =
                                                     FStarC_Syntax_Subst.compress
                                                       p1 in
                                                   uu___8.FStarC_Syntax_Syntax.n in
                                                 match uu___7 with
                                                 | FStarC_Syntax_Syntax.Tm_bvar
                                                     bv' when
                                                     FStarC_Syntax_Syntax.bv_eq
                                                       bv bv'
                                                     ->
                                                     (if
                                                        (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.wpe
                                                      then
                                                        FStarC_Compiler_Util.print_string
                                                          "WPE> Case 2\n"
                                                      else ();
                                                      (let q' =
                                                         FStarC_Syntax_Subst.subst
                                                           [FStarC_Syntax_Syntax.NT
                                                              (bv,
                                                                FStarC_Syntax_Util.t_false)]
                                                           q in
                                                       FStar_Pervasives_Native.Some
                                                         q'))
                                                 | uu___8 ->
                                                     FStar_Pervasives_Native.None))
                                       | FStar_Pervasives_Native.Some
                                           (FStarC_Syntax_Formula.QAll
                                           (bs, pats, phi1)) when
                                           types_match bs ->
                                           Obj.magic
                                             (Obj.repr
                                                (let uu___6 =
                                                   FStarC_Syntax_Formula.destruct_typ_as_formula
                                                     phi1 in
                                                 match uu___6 with
                                                 | FStar_Pervasives_Native.None
                                                     ->
                                                     Obj.repr
                                                       (let uu___7 =
                                                          is_applied_maybe_squashed
                                                            cfg bs phi1 in
                                                        FStarC_Class_Monad.op_let_Bang
                                                          FStarC_Class_Monad.monad_option
                                                          () ()
                                                          (Obj.magic uu___7)
                                                          (fun uu___8 ->
                                                             (fun bv' ->
                                                                let bv' =
                                                                  Obj.magic
                                                                    bv' in
                                                                let uu___8 =
                                                                  let uu___9
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_eq
                                                                    bv bv' in
                                                                  guard
                                                                    uu___9 in
                                                                Obj.magic
                                                                  (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Class_Monad.monad_option
                                                                    () ()
                                                                    uu___8
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    uu___9 in
                                                                    if
                                                                    (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.wpe
                                                                    then
                                                                    FStarC_Compiler_Util.print_string
                                                                    "WPE> Case 3\n"
                                                                    else ();
                                                                    (
                                                                    let uu___11
                                                                    =
                                                                    replace_full_applications_with
                                                                    bv
                                                                    (FStarC_Compiler_List.length
                                                                    bs)
                                                                    FStarC_Syntax_Util.t_true
                                                                    q in
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    (q',
                                                                    chgd) ->
                                                                    let uu___12
                                                                    =
                                                                    guard
                                                                    chgd in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Class_Monad.monad_option
                                                                    () ()
                                                                    uu___12
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    Obj.magic
                                                                    uu___13 in
                                                                    Obj.magic
                                                                    (FStar_Pervasives_Native.Some
                                                                    q'))
                                                                    uu___13))))
                                                                    uu___9)))
                                                               uu___8))
                                                 | FStar_Pervasives_Native.Some
                                                     (FStarC_Syntax_Formula.BaseConn
                                                     (lid1, (p1, uu___7)::[]))
                                                     when
                                                     FStarC_Ident.lid_equals
                                                       lid1
                                                       FStarC_Parser_Const.not_lid
                                                     ->
                                                     Obj.repr
                                                       (let uu___8 =
                                                          is_applied_maybe_squashed
                                                            cfg bs p1 in
                                                        FStarC_Class_Monad.op_let_Bang
                                                          FStarC_Class_Monad.monad_option
                                                          () ()
                                                          (Obj.magic uu___8)
                                                          (fun uu___9 ->
                                                             (fun bv' ->
                                                                let bv' =
                                                                  Obj.magic
                                                                    bv' in
                                                                let uu___9 =
                                                                  let uu___10
                                                                    =
                                                                    FStarC_Syntax_Syntax.bv_eq
                                                                    bv bv' in
                                                                  guard
                                                                    uu___10 in
                                                                Obj.magic
                                                                  (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Class_Monad.monad_option
                                                                    () ()
                                                                    uu___9
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    uu___10 in
                                                                    if
                                                                    (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.wpe
                                                                    then
                                                                    FStarC_Compiler_Util.print_string
                                                                    "WPE> Case 4\n"
                                                                    else ();
                                                                    (
                                                                    let uu___12
                                                                    =
                                                                    replace_full_applications_with
                                                                    bv
                                                                    (FStarC_Compiler_List.length
                                                                    bs)
                                                                    FStarC_Syntax_Util.t_false
                                                                    q in
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    (q',
                                                                    chgd) ->
                                                                    let uu___13
                                                                    =
                                                                    guard
                                                                    chgd in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Class_Monad.monad_option
                                                                    () ()
                                                                    uu___13
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    Obj.magic
                                                                    uu___14 in
                                                                    Obj.magic
                                                                    (FStar_Pervasives_Native.Some
                                                                    q'))
                                                                    uu___14))))
                                                                    uu___10)))
                                                               uu___9))
                                                 | uu___7 ->
                                                     Obj.repr
                                                       FStar_Pervasives_Native.None))
                                       | uu___6 ->
                                           Obj.magic
                                             (Obj.repr
                                                FStar_Pervasives_Native.None) in
                                     FStarC_Class_Monad.op_let_Bang
                                       FStarC_Class_Monad.monad_option () ()
                                       (Obj.magic uu___4)
                                       (fun uu___5 ->
                                          (fun q' ->
                                             let q' = Obj.magic q' in
                                             let phi' =
                                               let uu___5 =
                                                 FStarC_Syntax_Syntax.fvar
                                                   FStarC_Parser_Const.imp_lid
                                                   FStar_Pervasives_Native.None in
                                               let uu___6 =
                                                 let uu___7 =
                                                   FStarC_Syntax_Syntax.as_arg
                                                     p in
                                                 let uu___8 =
                                                   let uu___9 =
                                                     FStarC_Syntax_Syntax.as_arg
                                                       q' in
                                                   [uu___9] in
                                                 uu___7 :: uu___8 in
                                               FStarC_Syntax_Util.mk_app
                                                 uu___5 uu___6 in
                                             Obj.magic
                                               (FStar_Pervasives_Native.Some
                                                  phi')) uu___5))))
                          | uu___1 ->
                              Obj.magic
                                (Obj.repr FStar_Pervasives_Native.None))
                         uu___1))) uu___2 uu___1 uu___
let (is_forall_const :
  FStarC_TypeChecker_Cfg.cfg ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun cfg ->
         fun phi ->
           let uu___ = FStarC_Syntax_Formula.destruct_typ_as_formula phi in
           match uu___ with
           | FStar_Pervasives_Native.Some (FStarC_Syntax_Formula.QAll
               (b::[], uu___1, phi')) ->
               Obj.magic
                 (Obj.repr
                    (if
                       (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.wpe
                     then
                       (let uu___3 =
                          FStarC_Class_Show.show
                            FStarC_Syntax_Print.showable_bv
                            b.FStarC_Syntax_Syntax.binder_bv in
                        let uu___4 =
                          FStarC_Class_Show.show
                            FStarC_Syntax_Print.showable_term phi' in
                        FStarC_Compiler_Util.print2 "WPE> QAll [%s] %s\n"
                          uu___3 uu___4)
                     else ();
                     (let uu___3 =
                        is_quantified_const cfg
                          b.FStarC_Syntax_Syntax.binder_bv phi' in
                      FStarC_Class_Monad.op_let_Bang
                        FStarC_Class_Monad.monad_option () ()
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           (fun phi'1 ->
                              let phi'1 = Obj.magic phi'1 in
                              let uu___4 =
                                let uu___5 =
                                  (cfg.FStarC_TypeChecker_Cfg.tcenv).FStarC_TypeChecker_Env.universe_of
                                    cfg.FStarC_TypeChecker_Cfg.tcenv
                                    (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                FStarC_Syntax_Util.mk_forall uu___5
                                  b.FStarC_Syntax_Syntax.binder_bv phi'1 in
                              Obj.magic (FStar_Pervasives_Native.Some uu___4))
                             uu___4))))
           | uu___1 -> Obj.magic (Obj.repr FStar_Pervasives_Native.None))
        uu___1 uu___
let (is_extract_as_attr :
  FStarC_Syntax_Syntax.attribute ->
    FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun attr ->
    let uu___ = FStarC_Syntax_Util.head_and_args attr in
    match uu___ with
    | (head, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Syntax_Subst.compress head in
            uu___3.FStarC_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStarC_Syntax_Syntax.Tm_fvar fv, (t, uu___2)::[]) when
             FStarC_Syntax_Syntax.fv_eq_lid fv
               FStarC_Parser_Const.extract_as_lid
             ->
             let uu___3 =
               let uu___4 = FStarC_Syntax_Subst.compress t in
               uu___4.FStarC_Syntax_Syntax.n in
             (match uu___3 with
              | FStarC_Syntax_Syntax.Tm_quoted (impl, uu___4) ->
                  FStar_Pervasives_Native.Some impl
              | uu___4 -> FStar_Pervasives_Native.None)
         | uu___2 -> FStar_Pervasives_Native.None)
let (has_extract_as_attr :
  FStarC_TypeChecker_Env.env ->
    FStarC_Ident.lid ->
      FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun g ->
    fun lid ->
      let uu___ = FStarC_TypeChecker_Env.lookup_attrs_of_lid g lid in
      match uu___ with
      | FStar_Pervasives_Native.Some attrs ->
          FStarC_Compiler_Util.find_map attrs is_extract_as_attr
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let rec (norm :
  FStarC_TypeChecker_Cfg.cfg ->
    env -> stack -> FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun t ->
          let rec collapse_metas st =
            match st with
            | (Meta
                (uu___, FStarC_Syntax_Syntax.Meta_monadic uu___1, uu___2))::(Meta
                (e, FStarC_Syntax_Syntax.Meta_monadic m, r))::st' ->
                collapse_metas
                  ((Meta (e, (FStarC_Syntax_Syntax.Meta_monadic m), r)) ::
                  st')
            | uu___ -> st in
          let stack2 = collapse_metas stack1 in
          let t1 =
            if
              (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.norm_delayed
            then
              (match t.FStarC_Syntax_Syntax.n with
               | FStarC_Syntax_Syntax.Tm_delayed uu___1 ->
                   let uu___2 =
                     FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                       t in
                   FStarC_Compiler_Util.print1 "NORM delayed: %s\n" uu___2
               | uu___1 -> ())
            else ();
            FStarC_Syntax_Subst.compress t in
          FStarC_TypeChecker_Cfg.log cfg
            (fun uu___1 ->
               let uu___2 =
                 FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term
                   t1 in
               let uu___3 =
                 FStarC_Class_Show.show FStarC_Class_Show.showable_bool
                   (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.no_full_norm in
               let uu___4 =
                 FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
               let uu___5 =
                 FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                   (FStarC_Compiler_List.length env1) in
               let uu___6 =
                 let uu___7 =
                   let uu___8 = firstn (Prims.of_int (4)) stack2 in
                   FStar_Pervasives_Native.fst uu___8 in
                 FStarC_Class_Show.show
                   (FStarC_Class_Show.show_list showable_stack_elt) uu___7 in
               FStarC_Compiler_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s with %s env elements; top of the stack = %s\n"
                 uu___2 uu___3 uu___4 uu___5 uu___6);
          FStarC_TypeChecker_Cfg.log_cfg cfg
            (fun uu___2 ->
               let uu___3 =
                 FStarC_Class_Show.show FStarC_TypeChecker_Cfg.showable_cfg
                   cfg in
               FStarC_Compiler_Util.print1 ">>> cfg = %s\n" uu___3);
          (match t1.FStarC_Syntax_Syntax.n with
           | FStarC_Syntax_Syntax.Tm_unknown ->
               rebuild cfg empty_env stack2 t1
           | FStarC_Syntax_Syntax.Tm_constant uu___2 ->
               rebuild cfg empty_env stack2 t1
           | FStarC_Syntax_Syntax.Tm_name uu___2 ->
               rebuild cfg empty_env stack2 t1
           | FStarC_Syntax_Syntax.Tm_lazy uu___2 ->
               rebuild cfg empty_env stack2 t1
           | FStarC_Syntax_Syntax.Tm_fvar
               { FStarC_Syntax_Syntax.fv_name = uu___2;
                 FStarC_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStarC_Syntax_Syntax.Data_ctor);_}
               ->
               (FStarC_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu___4 ->
                     let uu___5 =
                       FStarC_Class_Show.show
                         FStarC_Syntax_Print.showable_term t1 in
                     FStarC_Compiler_Util.print1
                       " >> This is a constructor: %s\n" uu___5);
                rebuild cfg empty_env stack2 t1)
           | FStarC_Syntax_Syntax.Tm_fvar
               { FStarC_Syntax_Syntax.fv_name = uu___2;
                 FStarC_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStarC_Syntax_Syntax.Record_ctor uu___3);_}
               ->
               (FStarC_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu___5 ->
                     let uu___6 =
                       FStarC_Class_Show.show
                         FStarC_Syntax_Print.showable_term t1 in
                     FStarC_Compiler_Util.print1
                       " >> This is a constructor: %s\n" uu___6);
                rebuild cfg empty_env stack2 t1)
           | FStarC_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStarC_Syntax_Syntax.lid_of_fv fv in
               let qninfo =
                 FStarC_TypeChecker_Env.lookup_qname
                   cfg.FStarC_TypeChecker_Cfg.tcenv lid in
               let uu___2 =
                 FStarC_TypeChecker_Env.delta_depth_of_qninfo
                   cfg.FStarC_TypeChecker_Cfg.tcenv fv qninfo in
               (match uu___2 with
                | FStarC_Syntax_Syntax.Delta_constant_at_level uu___3 when
                    uu___3 = Prims.int_zero ->
                    (FStarC_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu___5 ->
                          let uu___6 =
                            FStarC_Class_Show.show
                              FStarC_Syntax_Print.showable_term t1 in
                          FStarC_Compiler_Util.print1
                            " >> This is a constant: %s\n" uu___6);
                     rebuild cfg empty_env stack2 t1)
                | uu___3 ->
                    let uu___4 = decide_unfolding cfg stack2 fv qninfo in
                    (match uu___4 with
                     | FStar_Pervasives_Native.Some
                         (FStar_Pervasives_Native.None, stack3) ->
                         do_unfold_fv cfg stack3 t1 qninfo fv
                     | FStar_Pervasives_Native.Some
                         (FStar_Pervasives_Native.Some cfg1, stack3) ->
                         let uu___5 = do_unfold_fv cfg1 [] t1 qninfo fv in
                         rebuild cfg1 empty_env stack3 uu___5
                     | FStar_Pervasives_Native.None ->
                         rebuild cfg empty_env stack2 t1))
           | FStarC_Syntax_Syntax.Tm_quoted (qt, qi) ->
               let qi1 =
                 FStarC_Syntax_Syntax.on_antiquoted (norm cfg env1 []) qi in
               let t2 =
                 FStarC_Syntax_Syntax.mk
                   (FStarC_Syntax_Syntax.Tm_quoted (qt, qi1))
                   t1.FStarC_Syntax_Syntax.pos in
               let uu___2 = closure_as_term cfg env1 t2 in
               rebuild cfg env1 stack2 uu___2
           | FStarC_Syntax_Syntax.Tm_app
               { FStarC_Syntax_Syntax.hd = hd;
                 FStarC_Syntax_Syntax.args = args;_}
               when
               (should_consider_norm_requests cfg) &&
                 (let uu___2 = is_norm_request hd args in
                  uu___2 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.print_normalized
                then
                  FStarC_Compiler_Util.print_string
                    "Rejigging norm request ... \n"
                else ();
                (let uu___3 = rejig_norm_request hd args in
                 norm cfg env1 stack2 uu___3))
           | FStarC_Syntax_Syntax.Tm_app
               { FStarC_Syntax_Syntax.hd = hd;
                 FStarC_Syntax_Syntax.args = args;_}
               when
               (should_consider_norm_requests cfg) &&
                 (let uu___2 = is_norm_request hd args in
                  uu___2 = Norm_request_ready)
               ->
               (if
                  (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.print_normalized
                then
                  (let uu___3 =
                     FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                       hd in
                   let uu___4 = FStarC_Syntax_Print.args_to_string args in
                   FStarC_Compiler_Util.print2
                     "Potential norm request with hd = %s and args = %s ... \n"
                     uu___3 uu___4)
                else ();
                (let cfg' =
                   {
                     FStarC_TypeChecker_Cfg.steps =
                       (let uu___3 = cfg.FStarC_TypeChecker_Cfg.steps in
                        {
                          FStarC_TypeChecker_Cfg.beta =
                            (uu___3.FStarC_TypeChecker_Cfg.beta);
                          FStarC_TypeChecker_Cfg.iota =
                            (uu___3.FStarC_TypeChecker_Cfg.iota);
                          FStarC_TypeChecker_Cfg.zeta =
                            (uu___3.FStarC_TypeChecker_Cfg.zeta);
                          FStarC_TypeChecker_Cfg.zeta_full =
                            (uu___3.FStarC_TypeChecker_Cfg.zeta_full);
                          FStarC_TypeChecker_Cfg.weak =
                            (uu___3.FStarC_TypeChecker_Cfg.weak);
                          FStarC_TypeChecker_Cfg.hnf =
                            (uu___3.FStarC_TypeChecker_Cfg.hnf);
                          FStarC_TypeChecker_Cfg.primops =
                            (uu___3.FStarC_TypeChecker_Cfg.primops);
                          FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStarC_TypeChecker_Cfg.unfold_until =
                            (uu___3.FStarC_TypeChecker_Cfg.unfold_until);
                          FStarC_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStarC_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStarC_TypeChecker_Cfg.unfold_attr =
                            (uu___3.FStarC_TypeChecker_Cfg.unfold_attr);
                          FStarC_TypeChecker_Cfg.unfold_qual =
                            (uu___3.FStarC_TypeChecker_Cfg.unfold_qual);
                          FStarC_TypeChecker_Cfg.unfold_namespace =
                            (uu___3.FStarC_TypeChecker_Cfg.unfold_namespace);
                          FStarC_TypeChecker_Cfg.dont_unfold_attr =
                            (uu___3.FStarC_TypeChecker_Cfg.dont_unfold_attr);
                          FStarC_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___3.FStarC_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStarC_TypeChecker_Cfg.simplify =
                            (uu___3.FStarC_TypeChecker_Cfg.simplify);
                          FStarC_TypeChecker_Cfg.erase_universes =
                            (uu___3.FStarC_TypeChecker_Cfg.erase_universes);
                          FStarC_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___3.FStarC_TypeChecker_Cfg.allow_unbound_universes);
                          FStarC_TypeChecker_Cfg.reify_ =
                            (uu___3.FStarC_TypeChecker_Cfg.reify_);
                          FStarC_TypeChecker_Cfg.compress_uvars =
                            (uu___3.FStarC_TypeChecker_Cfg.compress_uvars);
                          FStarC_TypeChecker_Cfg.no_full_norm =
                            (uu___3.FStarC_TypeChecker_Cfg.no_full_norm);
                          FStarC_TypeChecker_Cfg.check_no_uvars =
                            (uu___3.FStarC_TypeChecker_Cfg.check_no_uvars);
                          FStarC_TypeChecker_Cfg.unmeta =
                            (uu___3.FStarC_TypeChecker_Cfg.unmeta);
                          FStarC_TypeChecker_Cfg.unascribe =
                            (uu___3.FStarC_TypeChecker_Cfg.unascribe);
                          FStarC_TypeChecker_Cfg.in_full_norm_request =
                            (uu___3.FStarC_TypeChecker_Cfg.in_full_norm_request);
                          FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___3.FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStarC_TypeChecker_Cfg.nbe_step =
                            (uu___3.FStarC_TypeChecker_Cfg.nbe_step);
                          FStarC_TypeChecker_Cfg.for_extraction =
                            (uu___3.FStarC_TypeChecker_Cfg.for_extraction);
                          FStarC_TypeChecker_Cfg.unrefine =
                            (uu___3.FStarC_TypeChecker_Cfg.unrefine);
                          FStarC_TypeChecker_Cfg.default_univs_to_zero =
                            (uu___3.FStarC_TypeChecker_Cfg.default_univs_to_zero);
                          FStarC_TypeChecker_Cfg.tactics =
                            (uu___3.FStarC_TypeChecker_Cfg.tactics)
                        });
                     FStarC_TypeChecker_Cfg.tcenv =
                       (cfg.FStarC_TypeChecker_Cfg.tcenv);
                     FStarC_TypeChecker_Cfg.debug =
                       (cfg.FStarC_TypeChecker_Cfg.debug);
                     FStarC_TypeChecker_Cfg.delta_level =
                       [FStarC_TypeChecker_Env.Unfold
                          FStarC_Syntax_Syntax.delta_constant];
                     FStarC_TypeChecker_Cfg.primitive_steps =
                       (cfg.FStarC_TypeChecker_Cfg.primitive_steps);
                     FStarC_TypeChecker_Cfg.strong =
                       (cfg.FStarC_TypeChecker_Cfg.strong);
                     FStarC_TypeChecker_Cfg.memoize_lazy =
                       (cfg.FStarC_TypeChecker_Cfg.memoize_lazy);
                     FStarC_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStarC_TypeChecker_Cfg.reifying =
                       (cfg.FStarC_TypeChecker_Cfg.reifying);
                     FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
                       (cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
                   } in
                 let uu___3 = get_norm_request cfg (norm cfg' env1 []) args in
                 match uu___3 with
                 | FStar_Pervasives_Native.None ->
                     (if
                        (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.print_normalized
                      then
                        FStarC_Compiler_Util.print_string
                          "Norm request None ... \n"
                      else ();
                      (let stack3 =
                         FStarC_Compiler_List.fold_right
                           (fun uu___5 ->
                              fun stack4 ->
                                match uu___5 with
                                | (a, aq) ->
                                    let uu___6 =
                                      let uu___7 =
                                        let uu___8 =
                                          let uu___9 =
                                            let uu___10 = fresh_memo () in
                                            (env1, a, uu___10, false) in
                                          Clos uu___9 in
                                        (uu___8, aq,
                                          (t1.FStarC_Syntax_Syntax.pos)) in
                                      Arg uu___7 in
                                    uu___6 :: stack4) args stack2 in
                       FStarC_TypeChecker_Cfg.log cfg
                         (fun uu___6 ->
                            let uu___7 =
                              FStarC_Compiler_Util.string_of_int
                                (FStarC_Compiler_List.length args) in
                            FStarC_Compiler_Util.print1
                              "\tPushed %s arguments\n" uu___7);
                       norm cfg env1 stack3 hd))
                 | FStar_Pervasives_Native.Some (s, tm) when is_nbe_request s
                     ->
                     let tm' = closure_as_term cfg env1 tm in
                     let start = FStarC_Compiler_Util.now () in
                     let tm_norm = nbe_eval cfg s tm' in
                     let fin = FStarC_Compiler_Util.now () in
                     (if
                        (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.print_normalized
                      then
                        (let cfg'1 =
                           FStarC_TypeChecker_Cfg.config s
                             cfg.FStarC_TypeChecker_Cfg.tcenv in
                         let uu___5 =
                           let uu___6 =
                             let uu___7 =
                               FStarC_Compiler_Util.time_diff start fin in
                             FStar_Pervasives_Native.snd uu___7 in
                           FStarC_Class_Show.show
                             FStarC_Class_Show.showable_int uu___6 in
                         let uu___6 =
                           FStarC_Class_Show.show
                             FStarC_Syntax_Print.showable_term tm' in
                         let uu___7 =
                           FStarC_Class_Show.show
                             FStarC_TypeChecker_Cfg.showable_cfg cfg'1 in
                         let uu___8 =
                           FStarC_Class_Show.show
                             FStarC_Syntax_Print.showable_term tm_norm in
                         FStarC_Compiler_Util.print4
                           "NBE result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                           uu___5 uu___6 uu___7 uu___8)
                      else ();
                      rebuild cfg env1 stack2 tm_norm)
                 | FStar_Pervasives_Native.Some (s, tm) ->
                     (if
                        (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.print_normalized
                      then
                        (let uu___5 =
                           let uu___6 =
                             let uu___7 =
                               let uu___8 =
                                 FStarC_Class_Show.show
                                   FStarC_Syntax_Print.showable_term tm in
                               FStarC_Compiler_Util.format1
                                 "Starting norm request on `%s`." uu___8 in
                             FStarC_Errors_Msg.text uu___7 in
                           let uu___7 =
                             let uu___8 =
                               let uu___9 = FStarC_Errors_Msg.text "Steps =" in
                               let uu___10 =
                                 let uu___11 =
                                   FStarC_Class_Show.show
                                     (FStarC_Class_Show.show_list
                                        FStarC_TypeChecker_Env.showable_step)
                                     s in
                                 FStarC_Errors_Msg.text uu___11 in
                               FStarC_Pprint.op_Hat_Slash_Hat uu___9 uu___10 in
                             [uu___8] in
                           uu___6 :: uu___7 in
                         FStarC_Errors.diag
                           FStarC_Class_HasRange.hasRange_range
                           tm.FStarC_Syntax_Syntax.pos ()
                           (Obj.magic
                              FStarC_Errors_Msg.is_error_message_list_doc)
                           (Obj.magic uu___5))
                      else ();
                      (let delta_level =
                         let uu___5 =
                           FStarC_Compiler_Util.for_some
                             (fun uu___6 ->
                                match uu___6 with
                                | FStarC_TypeChecker_Env.UnfoldUntil uu___7
                                    -> true
                                | FStarC_TypeChecker_Env.UnfoldOnly uu___7 ->
                                    true
                                | FStarC_TypeChecker_Env.UnfoldFully uu___7
                                    -> true
                                | uu___7 -> false) s in
                         if uu___5
                         then
                           [FStarC_TypeChecker_Env.Unfold
                              FStarC_Syntax_Syntax.delta_constant]
                         else
                           if
                             (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
                           then
                             [FStarC_TypeChecker_Env.Eager_unfolding_only;
                             FStarC_TypeChecker_Env.InliningDelta]
                           else [FStarC_TypeChecker_Env.NoDelta] in
                       let cfg'1 =
                         let uu___5 =
                           let uu___6 = FStarC_TypeChecker_Cfg.to_fsteps s in
                           {
                             FStarC_TypeChecker_Cfg.beta =
                               (uu___6.FStarC_TypeChecker_Cfg.beta);
                             FStarC_TypeChecker_Cfg.iota =
                               (uu___6.FStarC_TypeChecker_Cfg.iota);
                             FStarC_TypeChecker_Cfg.zeta =
                               (uu___6.FStarC_TypeChecker_Cfg.zeta);
                             FStarC_TypeChecker_Cfg.zeta_full =
                               (uu___6.FStarC_TypeChecker_Cfg.zeta_full);
                             FStarC_TypeChecker_Cfg.weak =
                               (uu___6.FStarC_TypeChecker_Cfg.weak);
                             FStarC_TypeChecker_Cfg.hnf =
                               (uu___6.FStarC_TypeChecker_Cfg.hnf);
                             FStarC_TypeChecker_Cfg.primops =
                               (uu___6.FStarC_TypeChecker_Cfg.primops);
                             FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___6.FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStarC_TypeChecker_Cfg.unfold_until =
                               (uu___6.FStarC_TypeChecker_Cfg.unfold_until);
                             FStarC_TypeChecker_Cfg.unfold_only =
                               (uu___6.FStarC_TypeChecker_Cfg.unfold_only);
                             FStarC_TypeChecker_Cfg.unfold_fully =
                               (uu___6.FStarC_TypeChecker_Cfg.unfold_fully);
                             FStarC_TypeChecker_Cfg.unfold_attr =
                               (uu___6.FStarC_TypeChecker_Cfg.unfold_attr);
                             FStarC_TypeChecker_Cfg.unfold_qual =
                               (uu___6.FStarC_TypeChecker_Cfg.unfold_qual);
                             FStarC_TypeChecker_Cfg.unfold_namespace =
                               (uu___6.FStarC_TypeChecker_Cfg.unfold_namespace);
                             FStarC_TypeChecker_Cfg.dont_unfold_attr =
                               (uu___6.FStarC_TypeChecker_Cfg.dont_unfold_attr);
                             FStarC_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___6.FStarC_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStarC_TypeChecker_Cfg.simplify =
                               (uu___6.FStarC_TypeChecker_Cfg.simplify);
                             FStarC_TypeChecker_Cfg.erase_universes =
                               (uu___6.FStarC_TypeChecker_Cfg.erase_universes);
                             FStarC_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___6.FStarC_TypeChecker_Cfg.allow_unbound_universes);
                             FStarC_TypeChecker_Cfg.reify_ =
                               (uu___6.FStarC_TypeChecker_Cfg.reify_);
                             FStarC_TypeChecker_Cfg.compress_uvars =
                               (uu___6.FStarC_TypeChecker_Cfg.compress_uvars);
                             FStarC_TypeChecker_Cfg.no_full_norm =
                               (uu___6.FStarC_TypeChecker_Cfg.no_full_norm);
                             FStarC_TypeChecker_Cfg.check_no_uvars =
                               (uu___6.FStarC_TypeChecker_Cfg.check_no_uvars);
                             FStarC_TypeChecker_Cfg.unmeta =
                               (uu___6.FStarC_TypeChecker_Cfg.unmeta);
                             FStarC_TypeChecker_Cfg.unascribe =
                               (uu___6.FStarC_TypeChecker_Cfg.unascribe);
                             FStarC_TypeChecker_Cfg.in_full_norm_request =
                               true;
                             FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___6.FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStarC_TypeChecker_Cfg.nbe_step =
                               (uu___6.FStarC_TypeChecker_Cfg.nbe_step);
                             FStarC_TypeChecker_Cfg.for_extraction =
                               ((cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction);
                             FStarC_TypeChecker_Cfg.unrefine =
                               (uu___6.FStarC_TypeChecker_Cfg.unrefine);
                             FStarC_TypeChecker_Cfg.default_univs_to_zero =
                               (uu___6.FStarC_TypeChecker_Cfg.default_univs_to_zero);
                             FStarC_TypeChecker_Cfg.tactics =
                               (uu___6.FStarC_TypeChecker_Cfg.tactics)
                           } in
                         {
                           FStarC_TypeChecker_Cfg.steps = uu___5;
                           FStarC_TypeChecker_Cfg.tcenv =
                             (cfg.FStarC_TypeChecker_Cfg.tcenv);
                           FStarC_TypeChecker_Cfg.debug =
                             (cfg.FStarC_TypeChecker_Cfg.debug);
                           FStarC_TypeChecker_Cfg.delta_level = delta_level;
                           FStarC_TypeChecker_Cfg.primitive_steps =
                             (cfg.FStarC_TypeChecker_Cfg.primitive_steps);
                           FStarC_TypeChecker_Cfg.strong =
                             (cfg.FStarC_TypeChecker_Cfg.strong);
                           FStarC_TypeChecker_Cfg.memoize_lazy =
                             (cfg.FStarC_TypeChecker_Cfg.memoize_lazy);
                           FStarC_TypeChecker_Cfg.normalize_pure_lets = true;
                           FStarC_TypeChecker_Cfg.reifying =
                             (cfg.FStarC_TypeChecker_Cfg.reifying);
                           FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
                             (cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
                         } in
                       let t0 = FStarC_Compiler_Util.now () in
                       let uu___5 =
                         FStarC_Compiler_Util.record_time
                           (fun uu___6 -> norm cfg'1 env1 [] tm) in
                       match uu___5 with
                       | (tm_normed, ms) ->
                           (maybe_debug cfg tm_normed
                              (FStar_Pervasives_Native.Some (tm, t0));
                            rebuild cfg env1 stack2 tm_normed)))))
           | FStarC_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env1 u in
               let uu___2 =
                 FStarC_Syntax_Syntax.mk (FStarC_Syntax_Syntax.Tm_type u1)
                   t1.FStarC_Syntax_Syntax.pos in
               rebuild cfg env1 stack2 uu___2
           | FStarC_Syntax_Syntax.Tm_uinst (t', us) ->
               if
                 (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.erase_universes
               then norm cfg env1 stack2 t'
               else
                 (let us1 =
                    let uu___3 =
                      let uu___4 =
                        FStarC_Compiler_List.map (norm_universe cfg env1) us in
                      (uu___4, (t1.FStarC_Syntax_Syntax.pos)) in
                    UnivArgs uu___3 in
                  let stack3 = us1 :: stack2 in norm cfg env1 stack3 t')
           | FStarC_Syntax_Syntax.Tm_bvar x ->
               let uu___2 = lookup_bvar env1 x in
               (match uu___2 with
                | Univ uu___3 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy -> failwith "Term variable not found"
                | Clos (env2, t0, r, fix) ->
                    if
                      ((Prims.op_Negation fix) ||
                         (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.zeta)
                        ||
                        (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.zeta_full
                    then
                      let uu___3 = read_memo cfg r in
                      (match uu___3 with
                       | FStar_Pervasives_Native.Some (env3, t') ->
                           (FStarC_TypeChecker_Cfg.log cfg
                              (fun uu___5 ->
                                 let uu___6 =
                                   FStarC_Class_Show.show
                                     FStarC_Syntax_Print.showable_term t1 in
                                 let uu___7 =
                                   FStarC_Class_Show.show
                                     FStarC_Syntax_Print.showable_term t' in
                                 FStarC_Compiler_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu___6
                                   uu___7);
                            (let uu___5 = maybe_weakly_reduced t' in
                             if uu___5
                             then
                               match stack2 with
                               | [] when
                                   (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env3 stack2 t'
                               | uu___6 -> norm cfg env3 stack2 t'
                             else rebuild cfg env3 stack2 t'))
                       | FStar_Pervasives_Native.None ->
                           norm cfg env2 ((MemoLazy r) :: stack2) t0)
                    else norm cfg env2 stack2 t0)
           | FStarC_Syntax_Syntax.Tm_abs
               { FStarC_Syntax_Syntax.bs = bs;
                 FStarC_Syntax_Syntax.body = body;
                 FStarC_Syntax_Syntax.rc_opt = rc_opt;_}
               ->
               let rec maybe_strip_meta_divs stack3 =
                 match stack3 with
                 | [] -> FStar_Pervasives_Native.None
                 | (Meta
                     (uu___2, FStarC_Syntax_Syntax.Meta_monadic (m, uu___3),
                      uu___4))::tl
                     when
                     FStarC_Ident.lid_equals m
                       FStarC_Parser_Const.effect_DIV_lid
                     -> maybe_strip_meta_divs tl
                 | (Meta
                     (uu___2, FStarC_Syntax_Syntax.Meta_monadic_lift
                      (src, tgt, uu___3), uu___4))::tl
                     when
                     (FStarC_Ident.lid_equals src
                        FStarC_Parser_Const.effect_PURE_lid)
                       &&
                       (FStarC_Ident.lid_equals tgt
                          FStarC_Parser_Const.effect_DIV_lid)
                     -> maybe_strip_meta_divs tl
                 | (Arg uu___2)::uu___3 ->
                     FStar_Pervasives_Native.Some stack3
                 | uu___2 -> FStar_Pervasives_Native.None in
               let fallback uu___2 =
                 if
                   (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weak
                 then
                   let t2 = closure_as_term cfg env1 t1 in
                   rebuild cfg env1 stack2 t2
                 else
                   (let uu___4 = FStarC_Syntax_Subst.open_term' bs body in
                    match uu___4 with
                    | (bs1, body1, opening) ->
                        let env' =
                          FStarC_Compiler_List.fold_left
                            (fun env2 ->
                               fun uu___5 ->
                                 let uu___6 = dummy () in uu___6 :: env2)
                            env1 bs1 in
                        let rc_opt1 =
                          Obj.magic
                            (FStarC_Class_Monad.op_let_Bang
                               FStarC_Class_Monad.monad_option () ()
                               (Obj.magic rc_opt)
                               (fun uu___5 ->
                                  (fun rc ->
                                     let rc = Obj.magic rc in
                                     let rc1 = maybe_drop_rc_typ cfg rc in
                                     let uu___5 =
                                       let uu___6 =
                                         FStarC_Compiler_Util.map_option
                                           (FStarC_Syntax_Subst.subst opening)
                                           rc1.FStarC_Syntax_Syntax.residual_typ in
                                       {
                                         FStarC_Syntax_Syntax.residual_effect
                                           =
                                           (rc1.FStarC_Syntax_Syntax.residual_effect);
                                         FStarC_Syntax_Syntax.residual_typ =
                                           uu___6;
                                         FStarC_Syntax_Syntax.residual_flags
                                           =
                                           (rc1.FStarC_Syntax_Syntax.residual_flags)
                                       } in
                                     Obj.magic
                                       (FStar_Pervasives_Native.Some uu___5))
                                    uu___5)) in
                        (FStarC_TypeChecker_Cfg.log cfg
                           (fun uu___6 ->
                              let uu___7 =
                                FStarC_Compiler_Util.string_of_int
                                  (FStarC_Compiler_List.length bs1) in
                              FStarC_Compiler_Util.print1
                                "\tShifted %s dummies\n" uu___7);
                         (let cfg' =
                            {
                              FStarC_TypeChecker_Cfg.steps =
                                (cfg.FStarC_TypeChecker_Cfg.steps);
                              FStarC_TypeChecker_Cfg.tcenv =
                                (cfg.FStarC_TypeChecker_Cfg.tcenv);
                              FStarC_TypeChecker_Cfg.debug =
                                (cfg.FStarC_TypeChecker_Cfg.debug);
                              FStarC_TypeChecker_Cfg.delta_level =
                                (cfg.FStarC_TypeChecker_Cfg.delta_level);
                              FStarC_TypeChecker_Cfg.primitive_steps =
                                (cfg.FStarC_TypeChecker_Cfg.primitive_steps);
                              FStarC_TypeChecker_Cfg.strong = true;
                              FStarC_TypeChecker_Cfg.memoize_lazy =
                                (cfg.FStarC_TypeChecker_Cfg.memoize_lazy);
                              FStarC_TypeChecker_Cfg.normalize_pure_lets =
                                (cfg.FStarC_TypeChecker_Cfg.normalize_pure_lets);
                              FStarC_TypeChecker_Cfg.reifying =
                                (cfg.FStarC_TypeChecker_Cfg.reifying);
                              FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
                                (cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
                            } in
                          let body_norm =
                            norm cfg env'
                              [Abs
                                 (env1, bs1, env', rc_opt1,
                                   (t1.FStarC_Syntax_Syntax.pos))] body1 in
                          rebuild cfg env1 stack2 body_norm))) in
               (match stack2 with
                | (UnivArgs uu___2)::uu___3 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (Univ u, uu___2, uu___3))::stack_rest ->
                    let uu___4 =
                      let uu___5 =
                        let uu___6 = fresh_memo () in
                        (FStar_Pervasives_Native.None, (Univ u), uu___6) in
                      uu___5 :: env1 in
                    norm cfg uu___4 stack_rest t1
                | (Arg (c, uu___2, uu___3))::stack_rest ->
                    (match bs with
                     | [] -> failwith "Impossible"
                     | b::[] ->
                         (FStarC_TypeChecker_Cfg.log cfg
                            (fun uu___5 ->
                               let uu___6 =
                                 FStarC_Class_Show.show showable_closure c in
                               FStarC_Compiler_Util.print1 "\tShifted %s\n"
                                 uu___6);
                          (let uu___5 =
                             let uu___6 =
                               let uu___7 = fresh_memo () in
                               ((FStar_Pervasives_Native.Some b), c, uu___7) in
                             uu___6 :: env1 in
                           norm cfg uu___5 stack_rest body))
                     | b::tl ->
                         (FStarC_TypeChecker_Cfg.log cfg
                            (fun uu___5 ->
                               let uu___6 =
                                 FStarC_Class_Show.show showable_closure c in
                               FStarC_Compiler_Util.print1 "\tShifted %s\n"
                                 uu___6);
                          (let body1 =
                             FStarC_Syntax_Syntax.mk
                               (FStarC_Syntax_Syntax.Tm_abs
                                  {
                                    FStarC_Syntax_Syntax.bs = tl;
                                    FStarC_Syntax_Syntax.body = body;
                                    FStarC_Syntax_Syntax.rc_opt = rc_opt
                                  }) t1.FStarC_Syntax_Syntax.pos in
                           let uu___5 =
                             let uu___6 =
                               let uu___7 = fresh_memo () in
                               ((FStar_Pervasives_Native.Some b), c, uu___7) in
                             uu___6 :: env1 in
                           norm cfg uu___5 stack_rest body1)))
                | (MemoLazy r)::stack3 ->
                    (set_memo cfg r (env1, t1);
                     FStarC_TypeChecker_Cfg.log cfg
                       (fun uu___4 ->
                          let uu___5 =
                            FStarC_Class_Show.show
                              FStarC_Syntax_Print.showable_term t1 in
                          FStarC_Compiler_Util.print1 "\tSet memo %s\n"
                            uu___5);
                     norm cfg env1 stack3 t1)
                | (Meta uu___2)::uu___3 ->
                    let uu___4 = maybe_strip_meta_divs stack2 in
                    (match uu___4 with
                     | FStar_Pervasives_Native.None -> fallback ()
                     | FStar_Pervasives_Native.Some stack3 ->
                         norm cfg env1 stack3 t1)
                | (Match uu___2)::uu___3 -> fallback ()
                | (Let uu___2)::uu___3 -> fallback ()
                | (App uu___2)::uu___3 -> fallback ()
                | (CBVApp uu___2)::uu___3 -> fallback ()
                | (Abs uu___2)::uu___3 -> fallback ()
                | [] -> fallback ())
           | FStarC_Syntax_Syntax.Tm_app
               { FStarC_Syntax_Syntax.hd = head;
                 FStarC_Syntax_Syntax.args = args;_}
               ->
               let strict_args =
                 let uu___2 =
                   let uu___3 =
                     let uu___4 = FStarC_Syntax_Util.unascribe head in
                     FStarC_Syntax_Util.un_uinst uu___4 in
                   uu___3.FStarC_Syntax_Syntax.n in
                 match uu___2 with
                 | FStarC_Syntax_Syntax.Tm_fvar fv ->
                     FStarC_TypeChecker_Env.fv_has_strict_args
                       cfg.FStarC_TypeChecker_Cfg.tcenv fv
                 | uu___3 -> FStar_Pervasives_Native.None in
               (match strict_args with
                | FStar_Pervasives_Native.None ->
                    let stack3 =
                      FStarC_Compiler_List.fold_right
                        (fun uu___2 ->
                           fun stack4 ->
                             match uu___2 with
                             | (a, aq) ->
                                 let a1 =
                                   let uu___3 =
                                     (((let uu___4 =
                                          FStarC_TypeChecker_Cfg.cfg_env cfg in
                                        uu___4.FStarC_TypeChecker_Env.erase_erasable_args)
                                         ||
                                         (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction)
                                        ||
                                        (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.erase_erasable_args)
                                       &&
                                       (FStarC_Syntax_Util.aqual_is_erasable
                                          aq) in
                                   if uu___3
                                   then FStarC_Syntax_Util.exp_unit
                                   else a in
                                 let env2 =
                                   let uu___3 =
                                     let uu___4 =
                                       FStarC_Syntax_Subst.compress a1 in
                                     uu___4.FStarC_Syntax_Syntax.n in
                                   match uu___3 with
                                   | FStarC_Syntax_Syntax.Tm_name uu___4 ->
                                       empty_env
                                   | FStarC_Syntax_Syntax.Tm_constant uu___4
                                       -> empty_env
                                   | FStarC_Syntax_Syntax.Tm_lazy uu___4 ->
                                       empty_env
                                   | FStarC_Syntax_Syntax.Tm_fvar uu___4 ->
                                       empty_env
                                   | uu___4 -> env1 in
                                 let uu___3 =
                                   let uu___4 =
                                     let uu___5 =
                                       let uu___6 =
                                         let uu___7 = fresh_memo () in
                                         (env2, a1, uu___7, false) in
                                       Clos uu___6 in
                                     (uu___5, aq,
                                       (t1.FStarC_Syntax_Syntax.pos)) in
                                   Arg uu___4 in
                                 uu___3 :: stack4) args stack2 in
                    (FStarC_TypeChecker_Cfg.log cfg
                       (fun uu___3 ->
                          let uu___4 =
                            FStarC_Compiler_Util.string_of_int
                              (FStarC_Compiler_List.length args) in
                          FStarC_Compiler_Util.print1
                            "\tPushed %s arguments\n" uu___4);
                     norm cfg env1 stack3 head)
                | FStar_Pervasives_Native.Some strict_args1 ->
                    let norm_args =
                      FStarC_Compiler_List.map
                        (fun uu___2 ->
                           match uu___2 with
                           | (a, i) ->
                               let uu___3 = norm cfg env1 [] a in (uu___3, i))
                        args in
                    let norm_args_len = FStarC_Compiler_List.length norm_args in
                    let uu___2 =
                      FStarC_Compiler_List.for_all
                        (fun i ->
                           if i >= norm_args_len
                           then false
                           else
                             (let uu___4 =
                                FStarC_Compiler_List.nth norm_args i in
                              match uu___4 with
                              | (arg_i, uu___5) ->
                                  let uu___6 =
                                    let uu___7 =
                                      FStarC_Syntax_Util.unmeta_safe arg_i in
                                    FStarC_Syntax_Util.head_and_args uu___7 in
                                  (match uu___6 with
                                   | (head1, uu___7) ->
                                       let uu___8 =
                                         let uu___9 =
                                           FStarC_Syntax_Util.un_uinst head1 in
                                         uu___9.FStarC_Syntax_Syntax.n in
                                       (match uu___8 with
                                        | FStarC_Syntax_Syntax.Tm_constant
                                            uu___9 -> true
                                        | FStarC_Syntax_Syntax.Tm_fvar fv ->
                                            let uu___9 =
                                              FStarC_Syntax_Syntax.lid_of_fv
                                                fv in
                                            FStarC_TypeChecker_Env.is_datacon
                                              cfg.FStarC_TypeChecker_Cfg.tcenv
                                              uu___9
                                        | uu___9 -> false)))) strict_args1 in
                    if uu___2
                    then
                      let stack3 =
                        FStarC_Compiler_List.fold_right
                          (fun uu___3 ->
                             fun stack4 ->
                               match uu___3 with
                               | (a, aq) ->
                                   let uu___4 =
                                     let uu___5 =
                                       let uu___6 =
                                         let uu___7 =
                                           let uu___8 =
                                             FStarC_Compiler_Util.mk_ref
                                               (FStar_Pervasives_Native.Some
                                                  (cfg, ([], a))) in
                                           (env1, a, uu___8, false) in
                                         Clos uu___7 in
                                       (uu___6, aq,
                                         (t1.FStarC_Syntax_Syntax.pos)) in
                                     Arg uu___5 in
                                   uu___4 :: stack4) norm_args stack2 in
                      (FStarC_TypeChecker_Cfg.log cfg
                         (fun uu___4 ->
                            let uu___5 =
                              FStarC_Compiler_Util.string_of_int
                                (FStarC_Compiler_List.length args) in
                            FStarC_Compiler_Util.print1
                              "\tPushed %s arguments\n" uu___5);
                       norm cfg env1 stack3 head)
                    else
                      (let head1 = closure_as_term cfg env1 head in
                       let term =
                         FStarC_Syntax_Syntax.mk_Tm_app head1 norm_args
                           t1.FStarC_Syntax_Syntax.pos in
                       rebuild cfg env1 stack2 term))
           | FStarC_Syntax_Syntax.Tm_refine
               { FStarC_Syntax_Syntax.b = x;
                 FStarC_Syntax_Syntax.phi = uu___2;_}
               when
               (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
                 ||
                 (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.unrefine
               -> norm cfg env1 stack2 x.FStarC_Syntax_Syntax.sort
           | FStarC_Syntax_Syntax.Tm_refine
               { FStarC_Syntax_Syntax.b = x; FStarC_Syntax_Syntax.phi = f;_}
               ->
               if
                 (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weak
               then
                 (match (env1, stack2) with
                  | ([], []) ->
                      let t_x = norm cfg env1 [] x.FStarC_Syntax_Syntax.sort in
                      let t2 =
                        FStarC_Syntax_Syntax.mk
                          (FStarC_Syntax_Syntax.Tm_refine
                             {
                               FStarC_Syntax_Syntax.b =
                                 {
                                   FStarC_Syntax_Syntax.ppname =
                                     (x.FStarC_Syntax_Syntax.ppname);
                                   FStarC_Syntax_Syntax.index =
                                     (x.FStarC_Syntax_Syntax.index);
                                   FStarC_Syntax_Syntax.sort = t_x
                                 };
                               FStarC_Syntax_Syntax.phi = f
                             }) t1.FStarC_Syntax_Syntax.pos in
                      rebuild cfg env1 stack2 t2
                  | uu___2 ->
                      let uu___3 = closure_as_term cfg env1 t1 in
                      rebuild cfg env1 stack2 uu___3)
               else
                 (let t_x = norm cfg env1 [] x.FStarC_Syntax_Syntax.sort in
                  let uu___3 =
                    let uu___4 =
                      let uu___5 = FStarC_Syntax_Syntax.mk_binder x in
                      [uu___5] in
                    FStarC_Syntax_Subst.open_term uu___4 f in
                  match uu___3 with
                  | (closing, f1) ->
                      let f2 =
                        let uu___4 = let uu___5 = dummy () in uu___5 :: env1 in
                        norm cfg uu___4 [] f1 in
                      let t2 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 = FStarC_Syntax_Subst.close closing f2 in
                            {
                              FStarC_Syntax_Syntax.b =
                                {
                                  FStarC_Syntax_Syntax.ppname =
                                    (x.FStarC_Syntax_Syntax.ppname);
                                  FStarC_Syntax_Syntax.index =
                                    (x.FStarC_Syntax_Syntax.index);
                                  FStarC_Syntax_Syntax.sort = t_x
                                };
                              FStarC_Syntax_Syntax.phi = uu___6
                            } in
                          FStarC_Syntax_Syntax.Tm_refine uu___5 in
                        FStarC_Syntax_Syntax.mk uu___4
                          t1.FStarC_Syntax_Syntax.pos in
                      rebuild cfg env1 stack2 t2)
           | FStarC_Syntax_Syntax.Tm_arrow
               { FStarC_Syntax_Syntax.bs1 = bs;
                 FStarC_Syntax_Syntax.comp = c;_}
               ->
               if
                 (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weak
               then
                 let uu___2 = closure_as_term cfg env1 t1 in
                 rebuild cfg env1 stack2 uu___2
               else
                 (let uu___3 = FStarC_Syntax_Subst.open_comp bs c in
                  match uu___3 with
                  | (bs1, c1) ->
                      let c2 =
                        let uu___4 =
                          FStarC_Compiler_List.fold_left
                            (fun env2 ->
                               fun uu___5 ->
                                 let uu___6 = dummy () in uu___6 :: env2)
                            env1 bs1 in
                        norm_comp cfg uu___4 c1 in
                      let close_binders env2 bs2 =
                        let uu___4 = env_subst env2 in
                        FStarC_Syntax_Subst.subst_binders uu___4 bs2 in
                      let bs2 =
                        if
                          (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.hnf
                        then close_binders env1 bs1
                        else norm_binders cfg env1 bs1 in
                      let t2 = FStarC_Syntax_Util.arrow bs2 c2 in
                      rebuild cfg env1 stack2 t2)
           | FStarC_Syntax_Syntax.Tm_ascribed
               { FStarC_Syntax_Syntax.tm = t11;
                 FStarC_Syntax_Syntax.asc = uu___2;
                 FStarC_Syntax_Syntax.eff_opt = l;_}
               when
               (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.unascribe
               -> norm cfg env1 stack2 t11
           | FStarC_Syntax_Syntax.Tm_ascribed
               { FStarC_Syntax_Syntax.tm = t11;
                 FStarC_Syntax_Syntax.asc = asc;
                 FStarC_Syntax_Syntax.eff_opt = l;_}
               ->
               let rec stack_may_reduce s =
                 match s with
                 | (Match uu___2)::uu___3 when
                     (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.beta
                     -> true
                 | (Arg uu___2)::uu___3 when
                     (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.beta
                     -> true
                 | (App
                     (uu___2,
                      {
                        FStarC_Syntax_Syntax.n =
                          FStarC_Syntax_Syntax.Tm_constant
                          (FStarC_Const.Const_reify uu___3);
                        FStarC_Syntax_Syntax.pos = uu___4;
                        FStarC_Syntax_Syntax.vars = uu___5;
                        FStarC_Syntax_Syntax.hash_code = uu___6;_},
                      uu___7, uu___8))::uu___9
                     when
                     (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.beta
                     -> true
                 | (MemoLazy uu___2)::uu___3 when
                     (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.beta
                     -> true
                 | uu___2 -> false in
               let uu___2 = stack_may_reduce stack2 in
               if uu___2
               then
                 (FStarC_TypeChecker_Cfg.log cfg
                    (fun uu___4 ->
                       FStarC_Compiler_Util.print_string
                         "+++ Dropping ascription \n");
                  norm cfg env1 stack2 t11)
               else
                 (FStarC_TypeChecker_Cfg.log cfg
                    (fun uu___5 ->
                       FStarC_Compiler_Util.print_string
                         "+++ Keeping ascription \n");
                  (let t12 = norm cfg env1 [] t11 in
                   FStarC_TypeChecker_Cfg.log cfg
                     (fun uu___6 ->
                        FStarC_Compiler_Util.print_string
                          "+++ Normalizing ascription \n");
                   (let asc1 = norm_ascription cfg env1 asc in
                    let uu___6 =
                      let uu___7 =
                        let uu___8 =
                          let uu___9 = FStarC_Syntax_Util.unascribe t12 in
                          {
                            FStarC_Syntax_Syntax.tm = uu___9;
                            FStarC_Syntax_Syntax.asc = asc1;
                            FStarC_Syntax_Syntax.eff_opt = l
                          } in
                        FStarC_Syntax_Syntax.Tm_ascribed uu___8 in
                      FStarC_Syntax_Syntax.mk uu___7
                        t1.FStarC_Syntax_Syntax.pos in
                    rebuild cfg env1 stack2 uu___6)))
           | FStarC_Syntax_Syntax.Tm_match
               { FStarC_Syntax_Syntax.scrutinee = head;
                 FStarC_Syntax_Syntax.ret_opt = asc_opt;
                 FStarC_Syntax_Syntax.brs = branches1;
                 FStarC_Syntax_Syntax.rc_opt1 = lopt;_}
               ->
               let lopt1 =
                 FStarC_Compiler_Util.map_option (maybe_drop_rc_typ cfg) lopt in
               let stack3 =
                 (Match
                    (env1, asc_opt, branches1, lopt1, cfg,
                      (t1.FStarC_Syntax_Syntax.pos)))
                 :: stack2 in
               if
                 ((cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.iota
                    &&
                    (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee)
                   &&
                   (Prims.op_Negation
                      (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weak)
               then
                 let cfg' =
                   {
                     FStarC_TypeChecker_Cfg.steps =
                       (let uu___2 = cfg.FStarC_TypeChecker_Cfg.steps in
                        {
                          FStarC_TypeChecker_Cfg.beta =
                            (uu___2.FStarC_TypeChecker_Cfg.beta);
                          FStarC_TypeChecker_Cfg.iota =
                            (uu___2.FStarC_TypeChecker_Cfg.iota);
                          FStarC_TypeChecker_Cfg.zeta =
                            (uu___2.FStarC_TypeChecker_Cfg.zeta);
                          FStarC_TypeChecker_Cfg.zeta_full =
                            (uu___2.FStarC_TypeChecker_Cfg.zeta_full);
                          FStarC_TypeChecker_Cfg.weak = true;
                          FStarC_TypeChecker_Cfg.hnf =
                            (uu___2.FStarC_TypeChecker_Cfg.hnf);
                          FStarC_TypeChecker_Cfg.primops =
                            (uu___2.FStarC_TypeChecker_Cfg.primops);
                          FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___2.FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStarC_TypeChecker_Cfg.unfold_until =
                            (uu___2.FStarC_TypeChecker_Cfg.unfold_until);
                          FStarC_TypeChecker_Cfg.unfold_only =
                            (uu___2.FStarC_TypeChecker_Cfg.unfold_only);
                          FStarC_TypeChecker_Cfg.unfold_fully =
                            (uu___2.FStarC_TypeChecker_Cfg.unfold_fully);
                          FStarC_TypeChecker_Cfg.unfold_attr =
                            (uu___2.FStarC_TypeChecker_Cfg.unfold_attr);
                          FStarC_TypeChecker_Cfg.unfold_qual =
                            (uu___2.FStarC_TypeChecker_Cfg.unfold_qual);
                          FStarC_TypeChecker_Cfg.unfold_namespace =
                            (uu___2.FStarC_TypeChecker_Cfg.unfold_namespace);
                          FStarC_TypeChecker_Cfg.dont_unfold_attr =
                            (uu___2.FStarC_TypeChecker_Cfg.dont_unfold_attr);
                          FStarC_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___2.FStarC_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStarC_TypeChecker_Cfg.simplify =
                            (uu___2.FStarC_TypeChecker_Cfg.simplify);
                          FStarC_TypeChecker_Cfg.erase_universes =
                            (uu___2.FStarC_TypeChecker_Cfg.erase_universes);
                          FStarC_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___2.FStarC_TypeChecker_Cfg.allow_unbound_universes);
                          FStarC_TypeChecker_Cfg.reify_ =
                            (uu___2.FStarC_TypeChecker_Cfg.reify_);
                          FStarC_TypeChecker_Cfg.compress_uvars =
                            (uu___2.FStarC_TypeChecker_Cfg.compress_uvars);
                          FStarC_TypeChecker_Cfg.no_full_norm =
                            (uu___2.FStarC_TypeChecker_Cfg.no_full_norm);
                          FStarC_TypeChecker_Cfg.check_no_uvars =
                            (uu___2.FStarC_TypeChecker_Cfg.check_no_uvars);
                          FStarC_TypeChecker_Cfg.unmeta =
                            (uu___2.FStarC_TypeChecker_Cfg.unmeta);
                          FStarC_TypeChecker_Cfg.unascribe =
                            (uu___2.FStarC_TypeChecker_Cfg.unascribe);
                          FStarC_TypeChecker_Cfg.in_full_norm_request =
                            (uu___2.FStarC_TypeChecker_Cfg.in_full_norm_request);
                          FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___2.FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStarC_TypeChecker_Cfg.nbe_step =
                            (uu___2.FStarC_TypeChecker_Cfg.nbe_step);
                          FStarC_TypeChecker_Cfg.for_extraction =
                            (uu___2.FStarC_TypeChecker_Cfg.for_extraction);
                          FStarC_TypeChecker_Cfg.unrefine =
                            (uu___2.FStarC_TypeChecker_Cfg.unrefine);
                          FStarC_TypeChecker_Cfg.default_univs_to_zero =
                            (uu___2.FStarC_TypeChecker_Cfg.default_univs_to_zero);
                          FStarC_TypeChecker_Cfg.tactics =
                            (uu___2.FStarC_TypeChecker_Cfg.tactics)
                        });
                     FStarC_TypeChecker_Cfg.tcenv =
                       (cfg.FStarC_TypeChecker_Cfg.tcenv);
                     FStarC_TypeChecker_Cfg.debug =
                       (cfg.FStarC_TypeChecker_Cfg.debug);
                     FStarC_TypeChecker_Cfg.delta_level =
                       (cfg.FStarC_TypeChecker_Cfg.delta_level);
                     FStarC_TypeChecker_Cfg.primitive_steps =
                       (cfg.FStarC_TypeChecker_Cfg.primitive_steps);
                     FStarC_TypeChecker_Cfg.strong =
                       (cfg.FStarC_TypeChecker_Cfg.strong);
                     FStarC_TypeChecker_Cfg.memoize_lazy =
                       (cfg.FStarC_TypeChecker_Cfg.memoize_lazy);
                     FStarC_TypeChecker_Cfg.normalize_pure_lets =
                       (cfg.FStarC_TypeChecker_Cfg.normalize_pure_lets);
                     FStarC_TypeChecker_Cfg.reifying =
                       (cfg.FStarC_TypeChecker_Cfg.reifying);
                     FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
                       (cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
                   } in
                 let head_norm = norm cfg' env1 [] head in
                 rebuild cfg env1 stack3 head_norm
               else norm cfg env1 stack3 head
           | FStarC_Syntax_Syntax.Tm_let
               { FStarC_Syntax_Syntax.lbs = (b, lbs);
                 FStarC_Syntax_Syntax.body1 = lbody;_}
               when
               (FStarC_Syntax_Syntax.is_top_level lbs) &&
                 (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.compress_uvars
               ->
               let lbs1 =
                 FStarC_Compiler_List.map
                   (fun lb ->
                      let uu___2 =
                        FStarC_Syntax_Subst.univ_var_opening
                          lb.FStarC_Syntax_Syntax.lbunivs in
                      match uu___2 with
                      | (openings, lbunivs) ->
                          let cfg1 =
                            let uu___3 =
                              FStarC_TypeChecker_Env.push_univ_vars
                                cfg.FStarC_TypeChecker_Cfg.tcenv lbunivs in
                            {
                              FStarC_TypeChecker_Cfg.steps =
                                (cfg.FStarC_TypeChecker_Cfg.steps);
                              FStarC_TypeChecker_Cfg.tcenv = uu___3;
                              FStarC_TypeChecker_Cfg.debug =
                                (cfg.FStarC_TypeChecker_Cfg.debug);
                              FStarC_TypeChecker_Cfg.delta_level =
                                (cfg.FStarC_TypeChecker_Cfg.delta_level);
                              FStarC_TypeChecker_Cfg.primitive_steps =
                                (cfg.FStarC_TypeChecker_Cfg.primitive_steps);
                              FStarC_TypeChecker_Cfg.strong =
                                (cfg.FStarC_TypeChecker_Cfg.strong);
                              FStarC_TypeChecker_Cfg.memoize_lazy =
                                (cfg.FStarC_TypeChecker_Cfg.memoize_lazy);
                              FStarC_TypeChecker_Cfg.normalize_pure_lets =
                                (cfg.FStarC_TypeChecker_Cfg.normalize_pure_lets);
                              FStarC_TypeChecker_Cfg.reifying =
                                (cfg.FStarC_TypeChecker_Cfg.reifying);
                              FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
                                (cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
                            } in
                          let norm1 t2 =
                            let uu___3 =
                              let uu___4 =
                                FStarC_Syntax_Subst.subst openings t2 in
                              norm cfg1 env1 [] uu___4 in
                            FStarC_Syntax_Subst.close_univ_vars lbunivs
                              uu___3 in
                          let lbtyp = norm1 lb.FStarC_Syntax_Syntax.lbtyp in
                          let lbdef = norm1 lb.FStarC_Syntax_Syntax.lbdef in
                          {
                            FStarC_Syntax_Syntax.lbname =
                              (lb.FStarC_Syntax_Syntax.lbname);
                            FStarC_Syntax_Syntax.lbunivs = lbunivs;
                            FStarC_Syntax_Syntax.lbtyp = lbtyp;
                            FStarC_Syntax_Syntax.lbeff =
                              (lb.FStarC_Syntax_Syntax.lbeff);
                            FStarC_Syntax_Syntax.lbdef = lbdef;
                            FStarC_Syntax_Syntax.lbattrs =
                              (lb.FStarC_Syntax_Syntax.lbattrs);
                            FStarC_Syntax_Syntax.lbpos =
                              (lb.FStarC_Syntax_Syntax.lbpos)
                          }) lbs in
               let uu___2 =
                 FStarC_Syntax_Syntax.mk
                   (FStarC_Syntax_Syntax.Tm_let
                      {
                        FStarC_Syntax_Syntax.lbs = (b, lbs1);
                        FStarC_Syntax_Syntax.body1 = lbody
                      }) t1.FStarC_Syntax_Syntax.pos in
               rebuild cfg env1 stack2 uu___2
           | FStarC_Syntax_Syntax.Tm_let
               {
                 FStarC_Syntax_Syntax.lbs =
                   (uu___2,
                    {
                      FStarC_Syntax_Syntax.lbname = FStar_Pervasives.Inr
                        uu___3;
                      FStarC_Syntax_Syntax.lbunivs = uu___4;
                      FStarC_Syntax_Syntax.lbtyp = uu___5;
                      FStarC_Syntax_Syntax.lbeff = uu___6;
                      FStarC_Syntax_Syntax.lbdef = uu___7;
                      FStarC_Syntax_Syntax.lbattrs = uu___8;
                      FStarC_Syntax_Syntax.lbpos = uu___9;_}::uu___10);
                 FStarC_Syntax_Syntax.body1 = uu___11;_}
               -> rebuild cfg env1 stack2 t1
           | FStarC_Syntax_Syntax.Tm_let
               { FStarC_Syntax_Syntax.lbs = (false, lb::[]);
                 FStarC_Syntax_Syntax.body1 = body;_}
               ->
               let uu___2 =
                 FStarC_TypeChecker_Cfg.should_reduce_local_let cfg lb in
               if uu___2
               then
                 let binder =
                   let uu___3 =
                     FStarC_Compiler_Util.left lb.FStarC_Syntax_Syntax.lbname in
                   FStarC_Syntax_Syntax.mk_binder uu___3 in
                 let def =
                   FStarC_Syntax_Util.unmeta_lift
                     lb.FStarC_Syntax_Syntax.lbdef in
                 let env2 =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         let uu___6 = fresh_memo () in
                         (env1, def, uu___6, false) in
                       Clos uu___5 in
                     let uu___5 = fresh_memo () in
                     ((FStar_Pervasives_Native.Some binder), uu___4, uu___5) in
                   uu___3 :: env1 in
                 (FStarC_TypeChecker_Cfg.log cfg
                    (fun uu___4 ->
                       FStarC_Compiler_Util.print_string
                         "+++ Reducing Tm_let\n");
                  norm cfg env2 stack2 body)
               else
                 (let uu___4 =
                    (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.tactics
                      &&
                      (let uu___5 =
                         FStarC_TypeChecker_Env.norm_eff_name
                           cfg.FStarC_TypeChecker_Cfg.tcenv
                           lb.FStarC_Syntax_Syntax.lbeff in
                       FStarC_Syntax_Util.is_div_effect uu___5) in
                  if uu___4
                  then
                    let ffun =
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              let uu___9 =
                                FStarC_Compiler_Util.left
                                  lb.FStarC_Syntax_Syntax.lbname in
                              FStarC_Syntax_Syntax.mk_binder uu___9 in
                            [uu___8] in
                          {
                            FStarC_Syntax_Syntax.bs = uu___7;
                            FStarC_Syntax_Syntax.body = body;
                            FStarC_Syntax_Syntax.rc_opt =
                              FStar_Pervasives_Native.None
                          } in
                        FStarC_Syntax_Syntax.Tm_abs uu___6 in
                      FStarC_Syntax_Syntax.mk uu___5
                        t1.FStarC_Syntax_Syntax.pos in
                    let stack3 =
                      (CBVApp
                         (env1, ffun, FStar_Pervasives_Native.None,
                           (t1.FStarC_Syntax_Syntax.pos)))
                      :: stack2 in
                    (FStarC_TypeChecker_Cfg.log cfg
                       (fun uu___6 ->
                          FStarC_Compiler_Util.print_string
                            "+++ Evaluating DIV Tm_let\n");
                     norm cfg env1 stack3 lb.FStarC_Syntax_Syntax.lbdef)
                  else
                    if
                      (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weak
                    then
                      (FStarC_TypeChecker_Cfg.log cfg
                         (fun uu___7 ->
                            FStarC_Compiler_Util.print_string
                              "+++ Not touching Tm_let\n");
                       (let uu___7 = closure_as_term cfg env1 t1 in
                        rebuild cfg env1 stack2 uu___7))
                    else
                      (let uu___7 =
                         let uu___8 =
                           let uu___9 =
                             let uu___10 =
                               FStarC_Compiler_Util.left
                                 lb.FStarC_Syntax_Syntax.lbname in
                             FStarC_Syntax_Syntax.mk_binder uu___10 in
                           [uu___9] in
                         FStarC_Syntax_Subst.open_term uu___8 body in
                       match uu___7 with
                       | (bs, body1) ->
                           (FStarC_TypeChecker_Cfg.log cfg
                              (fun uu___9 ->
                                 FStarC_Compiler_Util.print_string
                                   "+++ Normalizing Tm_let -- type");
                            (let ty =
                               norm cfg env1 [] lb.FStarC_Syntax_Syntax.lbtyp in
                             let lbname =
                               let x =
                                 let uu___9 = FStarC_Compiler_List.hd bs in
                                 uu___9.FStarC_Syntax_Syntax.binder_bv in
                               FStar_Pervasives.Inl
                                 {
                                   FStarC_Syntax_Syntax.ppname =
                                     (x.FStarC_Syntax_Syntax.ppname);
                                   FStarC_Syntax_Syntax.index =
                                     (x.FStarC_Syntax_Syntax.index);
                                   FStarC_Syntax_Syntax.sort = ty
                                 } in
                             FStarC_TypeChecker_Cfg.log cfg
                               (fun uu___10 ->
                                  FStarC_Compiler_Util.print_string
                                    "+++ Normalizing Tm_let -- definiens\n");
                             (let lb1 =
                                let uu___10 =
                                  norm cfg env1 []
                                    lb.FStarC_Syntax_Syntax.lbdef in
                                let uu___11 =
                                  FStarC_Compiler_List.map (norm cfg env1 [])
                                    lb.FStarC_Syntax_Syntax.lbattrs in
                                {
                                  FStarC_Syntax_Syntax.lbname = lbname;
                                  FStarC_Syntax_Syntax.lbunivs =
                                    (lb.FStarC_Syntax_Syntax.lbunivs);
                                  FStarC_Syntax_Syntax.lbtyp = ty;
                                  FStarC_Syntax_Syntax.lbeff =
                                    (lb.FStarC_Syntax_Syntax.lbeff);
                                  FStarC_Syntax_Syntax.lbdef = uu___10;
                                  FStarC_Syntax_Syntax.lbattrs = uu___11;
                                  FStarC_Syntax_Syntax.lbpos =
                                    (lb.FStarC_Syntax_Syntax.lbpos)
                                } in
                              let env' =
                                FStarC_Compiler_List.fold_left
                                  (fun env2 ->
                                     fun uu___10 ->
                                       let uu___11 = dummy () in uu___11 ::
                                         env2) env1 bs in
                              FStarC_TypeChecker_Cfg.log cfg
                                (fun uu___11 ->
                                   FStarC_Compiler_Util.print_string
                                     "+++ Normalizing Tm_let -- body\n");
                              (let cfg' =
                                 {
                                   FStarC_TypeChecker_Cfg.steps =
                                     (cfg.FStarC_TypeChecker_Cfg.steps);
                                   FStarC_TypeChecker_Cfg.tcenv =
                                     (cfg.FStarC_TypeChecker_Cfg.tcenv);
                                   FStarC_TypeChecker_Cfg.debug =
                                     (cfg.FStarC_TypeChecker_Cfg.debug);
                                   FStarC_TypeChecker_Cfg.delta_level =
                                     (cfg.FStarC_TypeChecker_Cfg.delta_level);
                                   FStarC_TypeChecker_Cfg.primitive_steps =
                                     (cfg.FStarC_TypeChecker_Cfg.primitive_steps);
                                   FStarC_TypeChecker_Cfg.strong = true;
                                   FStarC_TypeChecker_Cfg.memoize_lazy =
                                     (cfg.FStarC_TypeChecker_Cfg.memoize_lazy);
                                   FStarC_TypeChecker_Cfg.normalize_pure_lets
                                     =
                                     (cfg.FStarC_TypeChecker_Cfg.normalize_pure_lets);
                                   FStarC_TypeChecker_Cfg.reifying =
                                     (cfg.FStarC_TypeChecker_Cfg.reifying);
                                   FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg
                                     =
                                     (cfg.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
                                 } in
                               let body_norm =
                                 norm cfg' env'
                                   [Let
                                      (env1, bs, lb1,
                                        (t1.FStarC_Syntax_Syntax.pos))] body1 in
                               rebuild cfg env1 stack2 body_norm))))))
           | FStarC_Syntax_Syntax.Tm_let
               { FStarC_Syntax_Syntax.lbs = (true, lbs);
                 FStarC_Syntax_Syntax.body1 = body;_}
               when
               (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.compress_uvars
                 ||
                 (((Prims.op_Negation
                      (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.zeta)
                     &&
                     (Prims.op_Negation
                        (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.zeta_full))
                    &&
                    (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.pure_subterms_within_computations)
               ->
               let uu___2 = FStarC_Syntax_Subst.open_let_rec lbs body in
               (match uu___2 with
                | (lbs1, body1) ->
                    let lbs2 =
                      FStarC_Compiler_List.map
                        (fun lb ->
                           let ty =
                             norm cfg env1 [] lb.FStarC_Syntax_Syntax.lbtyp in
                           let lbname =
                             let uu___3 =
                               let uu___4 =
                                 FStarC_Compiler_Util.left
                                   lb.FStarC_Syntax_Syntax.lbname in
                               {
                                 FStarC_Syntax_Syntax.ppname =
                                   (uu___4.FStarC_Syntax_Syntax.ppname);
                                 FStarC_Syntax_Syntax.index =
                                   (uu___4.FStarC_Syntax_Syntax.index);
                                 FStarC_Syntax_Syntax.sort = ty
                               } in
                             FStar_Pervasives.Inl uu___3 in
                           let uu___3 =
                             FStarC_Syntax_Util.abs_formals
                               lb.FStarC_Syntax_Syntax.lbdef in
                           match uu___3 with
                           | (xs, def_body, lopt) ->
                               let xs1 = norm_binders cfg env1 xs in
                               let env2 =
                                 let uu___4 =
                                   FStarC_Compiler_List.map
                                     (fun uu___5 -> dummy ()) xs1 in
                                 let uu___5 =
                                   let uu___6 =
                                     FStarC_Compiler_List.map
                                       (fun uu___7 -> dummy ()) lbs1 in
                                   FStarC_Compiler_List.op_At uu___6 env1 in
                                 FStarC_Compiler_List.op_At uu___4 uu___5 in
                               let def_body1 = norm cfg env2 [] def_body in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu___4 =
                                       let uu___5 =
                                         FStarC_Compiler_Util.map_opt
                                           rc.FStarC_Syntax_Syntax.residual_typ
                                           (norm cfg env2 []) in
                                       {
                                         FStarC_Syntax_Syntax.residual_effect
                                           =
                                           (rc.FStarC_Syntax_Syntax.residual_effect);
                                         FStarC_Syntax_Syntax.residual_typ =
                                           uu___5;
                                         FStarC_Syntax_Syntax.residual_flags
                                           =
                                           (rc.FStarC_Syntax_Syntax.residual_flags)
                                       } in
                                     FStar_Pervasives_Native.Some uu___4
                                 | uu___4 -> lopt in
                               let def =
                                 FStarC_Syntax_Util.abs xs1 def_body1 lopt1 in
                               {
                                 FStarC_Syntax_Syntax.lbname = lbname;
                                 FStarC_Syntax_Syntax.lbunivs =
                                   (lb.FStarC_Syntax_Syntax.lbunivs);
                                 FStarC_Syntax_Syntax.lbtyp = ty;
                                 FStarC_Syntax_Syntax.lbeff =
                                   (lb.FStarC_Syntax_Syntax.lbeff);
                                 FStarC_Syntax_Syntax.lbdef = def;
                                 FStarC_Syntax_Syntax.lbattrs =
                                   (lb.FStarC_Syntax_Syntax.lbattrs);
                                 FStarC_Syntax_Syntax.lbpos =
                                   (lb.FStarC_Syntax_Syntax.lbpos)
                               }) lbs1 in
                    let env' =
                      let uu___3 =
                        FStarC_Compiler_List.map (fun uu___4 -> dummy ())
                          lbs2 in
                      FStarC_Compiler_List.op_At uu___3 env1 in
                    let body2 = norm cfg env' [] body1 in
                    let uu___3 = FStarC_Syntax_Subst.close_let_rec lbs2 body2 in
                    (match uu___3 with
                     | (lbs3, body3) ->
                         let t2 =
                           {
                             FStarC_Syntax_Syntax.n =
                               (FStarC_Syntax_Syntax.Tm_let
                                  {
                                    FStarC_Syntax_Syntax.lbs = (true, lbs3);
                                    FStarC_Syntax_Syntax.body1 = body3
                                  });
                             FStarC_Syntax_Syntax.pos =
                               (t1.FStarC_Syntax_Syntax.pos);
                             FStarC_Syntax_Syntax.vars =
                               (t1.FStarC_Syntax_Syntax.vars);
                             FStarC_Syntax_Syntax.hash_code =
                               (t1.FStarC_Syntax_Syntax.hash_code)
                           } in
                         rebuild cfg env1 stack2 t2))
           | FStarC_Syntax_Syntax.Tm_let
               { FStarC_Syntax_Syntax.lbs = lbs;
                 FStarC_Syntax_Syntax.body1 = body;_}
               when
               (Prims.op_Negation
                  (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.zeta)
                 &&
                 (Prims.op_Negation
                    (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.zeta_full)
               ->
               let uu___2 = closure_as_term cfg env1 t1 in
               rebuild cfg env1 stack2 uu___2
           | FStarC_Syntax_Syntax.Tm_let
               { FStarC_Syntax_Syntax.lbs = lbs;
                 FStarC_Syntax_Syntax.body1 = body;_}
               ->
               let uu___2 =
                 FStarC_Compiler_List.fold_right
                   (fun lb ->
                      fun uu___3 ->
                        match uu___3 with
                        | (rec_env, memos, i) ->
                            let bv =
                              let uu___4 =
                                FStarC_Compiler_Util.left
                                  lb.FStarC_Syntax_Syntax.lbname in
                              {
                                FStarC_Syntax_Syntax.ppname =
                                  (uu___4.FStarC_Syntax_Syntax.ppname);
                                FStarC_Syntax_Syntax.index = i;
                                FStarC_Syntax_Syntax.sort =
                                  (uu___4.FStarC_Syntax_Syntax.sort)
                              } in
                            let f_i = FStarC_Syntax_Syntax.bv_to_tm bv in
                            let fix_f_i =
                              FStarC_Syntax_Syntax.mk
                                (FStarC_Syntax_Syntax.Tm_let
                                   {
                                     FStarC_Syntax_Syntax.lbs = lbs;
                                     FStarC_Syntax_Syntax.body1 = f_i
                                   }) t1.FStarC_Syntax_Syntax.pos in
                            let memo = fresh_memo () in
                            let rec_env1 =
                              let uu___4 =
                                let uu___5 = fresh_memo () in
                                (FStar_Pervasives_Native.None,
                                  (Clos (env1, fix_f_i, memo, true)), uu___5) in
                              uu___4 :: rec_env in
                            (rec_env1, (memo :: memos), (i + Prims.int_one)))
                   (FStar_Pervasives_Native.snd lbs)
                   (env1, [], Prims.int_zero) in
               (match uu___2 with
                | (rec_env, memos, uu___3) ->
                    let uu___4 =
                      FStarC_Compiler_List.map2
                        (fun lb ->
                           fun memo ->
                             FStarC_Compiler_Effect.op_Colon_Equals memo
                               (FStar_Pervasives_Native.Some
                                  (cfg,
                                    (rec_env,
                                      (lb.FStarC_Syntax_Syntax.lbdef)))))
                        (FStar_Pervasives_Native.snd lbs) memos in
                    let body_env =
                      FStarC_Compiler_List.fold_left
                        (fun env2 ->
                           fun lb ->
                             let uu___5 =
                               let uu___6 =
                                 let uu___7 =
                                   let uu___8 = fresh_memo () in
                                   (rec_env, (lb.FStarC_Syntax_Syntax.lbdef),
                                     uu___8, false) in
                                 Clos uu___7 in
                               let uu___7 = fresh_memo () in
                               (FStar_Pervasives_Native.None, uu___6, uu___7) in
                             uu___5 :: env2) env1
                        (FStar_Pervasives_Native.snd lbs) in
                    (FStarC_TypeChecker_Cfg.log cfg
                       (fun uu___6 ->
                          FStarC_Compiler_Util.print1
                            "reducing with knot %s\n" "");
                     norm cfg body_env stack2 body))
           | FStarC_Syntax_Syntax.Tm_meta
               { FStarC_Syntax_Syntax.tm2 = head;
                 FStarC_Syntax_Syntax.meta = m;_}
               ->
               (FStarC_TypeChecker_Cfg.log cfg
                  (fun uu___3 ->
                     let uu___4 =
                       FStarC_Class_Show.show
                         FStarC_Syntax_Print.showable_metadata m in
                     FStarC_Compiler_Util.print1 ">> metadata = %s\n" uu___4);
                (match m with
                 | FStarC_Syntax_Syntax.Meta_monadic (m_from, ty) ->
                     if
                       (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
                     then
                       let uu___3 =
                         (FStarC_TypeChecker_Env.is_erasable_effect
                            cfg.FStarC_TypeChecker_Cfg.tcenv m_from)
                           ||
                           ((FStarC_Syntax_Util.is_pure_effect m_from) &&
                              (FStarC_TypeChecker_Env.non_informative
                                 cfg.FStarC_TypeChecker_Cfg.tcenv ty)) in
                       (if uu___3
                        then
                          let uu___4 =
                            FStarC_Syntax_Syntax.mk
                              (FStarC_Syntax_Syntax.Tm_meta
                                 {
                                   FStarC_Syntax_Syntax.tm2 =
                                     FStarC_Syntax_Util.exp_unit;
                                   FStarC_Syntax_Syntax.meta = m
                                 }) t1.FStarC_Syntax_Syntax.pos in
                          rebuild cfg env1 stack2 uu___4
                        else
                          reduce_impure_comp cfg env1 stack2 head
                            (FStar_Pervasives.Inl m_from) ty)
                     else
                       reduce_impure_comp cfg env1 stack2 head
                         (FStar_Pervasives.Inl m_from) ty
                 | FStarC_Syntax_Syntax.Meta_monadic_lift (m_from, m_to, ty)
                     ->
                     if
                       (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
                     then
                       let uu___3 =
                         ((FStarC_TypeChecker_Env.is_erasable_effect
                             cfg.FStarC_TypeChecker_Cfg.tcenv m_from)
                            ||
                            (FStarC_TypeChecker_Env.is_erasable_effect
                               cfg.FStarC_TypeChecker_Cfg.tcenv m_to))
                           ||
                           ((FStarC_Syntax_Util.is_pure_effect m_from) &&
                              (FStarC_TypeChecker_Env.non_informative
                                 cfg.FStarC_TypeChecker_Cfg.tcenv ty)) in
                       (if uu___3
                        then
                          let uu___4 =
                            FStarC_Syntax_Syntax.mk
                              (FStarC_Syntax_Syntax.Tm_meta
                                 {
                                   FStarC_Syntax_Syntax.tm2 =
                                     FStarC_Syntax_Util.exp_unit;
                                   FStarC_Syntax_Syntax.meta = m
                                 }) t1.FStarC_Syntax_Syntax.pos in
                          rebuild cfg env1 stack2 uu___4
                        else
                          reduce_impure_comp cfg env1 stack2 head
                            (FStar_Pervasives.Inr (m_from, m_to)) ty)
                     else
                       reduce_impure_comp cfg env1 stack2 head
                         (FStar_Pervasives.Inr (m_from, m_to)) ty
                 | uu___3 ->
                     if
                       (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.unmeta
                     then norm cfg env1 stack2 head
                     else
                       (match stack2 with
                        | uu___5::uu___6 ->
                            (match m with
                             | FStarC_Syntax_Syntax.Meta_labeled
                                 (l, r, uu___7) ->
                                 norm cfg env1 ((Meta (env1, m, r)) ::
                                   stack2) head
                             | FStarC_Syntax_Syntax.Meta_pattern
                                 (names, args) ->
                                 let args1 = norm_pattern_args cfg env1 args in
                                 let names1 =
                                   FStarC_Compiler_List.map
                                     (norm cfg env1 []) names in
                                 norm cfg env1
                                   ((Meta
                                       (env1,
                                         (FStarC_Syntax_Syntax.Meta_pattern
                                            (names1, args1)),
                                         (t1.FStarC_Syntax_Syntax.pos))) ::
                                   stack2) head
                             | FStarC_Syntax_Syntax.Meta_desugared
                                 (FStarC_Syntax_Syntax.Sequence) when
                                 (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets
                                 ->
                                 norm cfg env1
                                   ((Meta
                                       (env1, m,
                                         (t1.FStarC_Syntax_Syntax.pos))) ::
                                   stack2) head
                             | FStarC_Syntax_Syntax.Meta_desugared
                                 (FStarC_Syntax_Syntax.Machine_integer
                                 (uu___7, uu___8)) ->
                                 norm cfg env1
                                   ((Meta
                                       (env1, m,
                                         (t1.FStarC_Syntax_Syntax.pos))) ::
                                   stack2) head
                             | uu___7 -> norm cfg env1 stack2 head)
                        | [] ->
                            let head1 = norm cfg env1 [] head in
                            let m1 =
                              match m with
                              | FStarC_Syntax_Syntax.Meta_pattern
                                  (names, args) ->
                                  let names1 =
                                    FStarC_Compiler_List.map
                                      (norm cfg env1 []) names in
                                  let uu___5 =
                                    let uu___6 =
                                      norm_pattern_args cfg env1 args in
                                    (names1, uu___6) in
                                  FStarC_Syntax_Syntax.Meta_pattern uu___5
                              | uu___5 -> m in
                            let t2 =
                              FStarC_Syntax_Syntax.mk
                                (FStarC_Syntax_Syntax.Tm_meta
                                   {
                                     FStarC_Syntax_Syntax.tm2 = head1;
                                     FStarC_Syntax_Syntax.meta = m1
                                   }) t1.FStarC_Syntax_Syntax.pos in
                            rebuild cfg env1 stack2 t2)))
           | FStarC_Syntax_Syntax.Tm_delayed uu___2 ->
               failwith "impossible: Tm_delayed on norm"
           | FStarC_Syntax_Syntax.Tm_uvar uu___2 ->
               (if
                  (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.check_no_uvars
                then
                  (let uu___4 =
                     let uu___5 =
                       FStarC_Class_Show.show
                         FStarC_Compiler_Range_Ops.showable_range
                         t1.FStarC_Syntax_Syntax.pos in
                     let uu___6 =
                       FStarC_Class_Show.show
                         FStarC_Syntax_Print.showable_term t1 in
                     FStarC_Compiler_Util.format2
                       "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                       uu___5 uu___6 in
                   failwith uu___4)
                else ();
                (let t2 =
                   FStarC_Errors.with_ctx "inlining"
                     (fun uu___4 -> closure_as_term cfg env1 t1) in
                 rebuild cfg env1 stack2 t2)))
and (do_unfold_fv :
  FStarC_TypeChecker_Cfg.cfg ->
    stack_elt Prims.list ->
      FStarC_Syntax_Syntax.term ->
        FStarC_TypeChecker_Env.qninfo ->
          FStarC_Syntax_Syntax.fv -> FStarC_Syntax_Syntax.term)
  =
  fun cfg ->
    fun stack1 ->
      fun t0 ->
        fun qninfo ->
          fun f ->
            let defn uu___ =
              FStarC_TypeChecker_Env.lookup_definition_qninfo
                cfg.FStarC_TypeChecker_Cfg.delta_level
                (f.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
                qninfo in
            let defn1 uu___ =
              if
                (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
              then
                match qninfo with
                | FStar_Pervasives_Native.Some
                    (FStar_Pervasives.Inr (se, FStar_Pervasives_Native.None),
                     uu___1)
                    when
                    FStarC_TypeChecker_Env.visible_with
                      cfg.FStarC_TypeChecker_Cfg.delta_level
                      se.FStarC_Syntax_Syntax.sigquals
                    ->
                    let uu___2 =
                      FStarC_Compiler_Util.find_map
                        se.FStarC_Syntax_Syntax.sigattrs is_extract_as_attr in
                    (match uu___2 with
                     | FStar_Pervasives_Native.Some impl ->
                         FStar_Pervasives_Native.Some ([], impl)
                     | FStar_Pervasives_Native.None -> defn ())
                | uu___1 -> defn ()
              else defn () in
            let uu___ = defn1 () in
            match uu___ with
            | FStar_Pervasives_Native.None ->
                (FStarC_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu___2 ->
                      let uu___3 =
                        FStarC_Class_Show.show
                          FStarC_Syntax_Print.showable_fv f in
                      let uu___4 =
                        FStarC_Class_Show.show
                          (FStarC_Class_Show.show_list
                             FStarC_TypeChecker_Env.showable_delta_level)
                          cfg.FStarC_TypeChecker_Cfg.delta_level in
                      FStarC_Compiler_Util.print2
                        " >> No definition found for %s (delta_level = %s)\n"
                        uu___3 uu___4);
                 rebuild cfg empty_env stack1 t0)
            | FStar_Pervasives_Native.Some (us, t) ->
                (FStarC_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu___2 ->
                      let uu___3 =
                        FStarC_Class_Show.show
                          FStarC_Syntax_Print.showable_term t0 in
                      let uu___4 =
                        FStarC_Class_Show.show
                          FStarC_Syntax_Print.showable_term t in
                      FStarC_Compiler_Util.print2 " >> Unfolded %s to %s\n"
                        uu___3 uu___4);
                 (let t1 =
                    if
                      (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.unfold_until
                        =
                        (FStar_Pervasives_Native.Some
                           FStarC_Syntax_Syntax.delta_constant)
                    then t
                    else
                      FStarC_Syntax_Subst.set_use_range
                        t0.FStarC_Syntax_Syntax.pos t in
                  let n = FStarC_Compiler_List.length us in
                  if n > Prims.int_zero
                  then
                    match stack1 with
                    | (UnivArgs (us', uu___2))::stack2 ->
                        ((let uu___4 =
                            FStarC_Compiler_Effect.op_Bang dbg_univ_norm in
                          if uu___4
                          then
                            FStarC_Compiler_List.iter
                              (fun x ->
                                 let uu___5 =
                                   FStarC_Class_Show.show
                                     FStarC_Syntax_Print.showable_univ x in
                                 FStarC_Compiler_Util.print1
                                   "Univ (normalizer) %s\n" uu___5) us'
                          else ());
                         (let env1 =
                            FStarC_Compiler_List.fold_left
                              (fun env2 ->
                                 fun u ->
                                   let uu___4 =
                                     let uu___5 = fresh_memo () in
                                     (FStar_Pervasives_Native.None, (
                                       Univ u), uu___5) in
                                   uu___4 :: env2) empty_env us' in
                          norm cfg env1 stack2 t1))
                    | uu___2 when
                        (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.erase_universes
                          ||
                          (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.allow_unbound_universes
                        -> norm cfg empty_env stack1 t1
                    | uu___2 ->
                        let uu___3 =
                          let uu___4 =
                            FStarC_Class_Show.show
                              FStarC_Ident.showable_lident
                              (f.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
                          FStarC_Compiler_Util.format1
                            "Impossible: missing universe instantiation on %s"
                            uu___4 in
                        failwith uu___3
                  else norm cfg empty_env stack1 t1))
and (reduce_impure_comp :
  FStarC_TypeChecker_Cfg.cfg ->
    env ->
      stack_elt Prims.list ->
        FStarC_Syntax_Syntax.term ->
          (FStarC_Syntax_Syntax.monad_name,
            (FStarC_Syntax_Syntax.monad_name *
              FStarC_Syntax_Syntax.monad_name))
            FStar_Pervasives.either ->
            FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun head ->
          fun m ->
            fun t ->
              let t1 = norm cfg env1 [] t in
              let metadata =
                match m with
                | FStar_Pervasives.Inl m1 ->
                    FStarC_Syntax_Syntax.Meta_monadic (m1, t1)
                | FStar_Pervasives.Inr (m1, m') ->
                    FStarC_Syntax_Syntax.Meta_monadic_lift (m1, m', t1) in
              norm cfg env1
                ((Meta (env1, metadata, (head.FStarC_Syntax_Syntax.pos))) ::
                stack1) head
and (do_reify_monadic :
  (unit -> FStarC_Syntax_Syntax.term) ->
    FStarC_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          FStarC_Syntax_Syntax.term ->
            FStarC_Syntax_Syntax.monad_name ->
              FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.term)
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
                        FStarC_Syntax_Syntax.n =
                          FStarC_Syntax_Syntax.Tm_constant
                          (FStarC_Const.Const_reify uu___2);
                        FStarC_Syntax_Syntax.pos = uu___3;
                        FStarC_Syntax_Syntax.vars = uu___4;
                        FStarC_Syntax_Syntax.hash_code = uu___5;_},
                      uu___6, uu___7))::uu___8
                     -> ()
                 | uu___1 ->
                     let uu___2 =
                       let uu___3 =
                         FStarC_Class_Show.show
                           (FStarC_Class_Show.show_list showable_stack_elt)
                           stack1 in
                       FStarC_Compiler_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu___3 in
                     failwith uu___2);
                (let top0 = top in
                 let top1 = FStarC_Syntax_Util.unascribe top in
                 FStarC_TypeChecker_Cfg.log cfg
                   (fun uu___2 ->
                      let uu___3 =
                        FStarC_Class_Tagged.tag_of
                          FStarC_Syntax_Syntax.tagged_term top1 in
                      let uu___4 =
                        FStarC_Class_Show.show
                          FStarC_Syntax_Print.showable_term top1 in
                      FStarC_Compiler_Util.print2 "Reifying: (%s) %s\n"
                        uu___3 uu___4);
                 (let top2 = FStarC_Syntax_Util.unmeta_safe top1 in
                  let uu___2 =
                    let uu___3 = FStarC_Syntax_Subst.compress top2 in
                    uu___3.FStarC_Syntax_Syntax.n in
                  match uu___2 with
                  | FStarC_Syntax_Syntax.Tm_let
                      { FStarC_Syntax_Syntax.lbs = (false, lb::[]);
                        FStarC_Syntax_Syntax.body1 = body;_}
                      ->
                      let eff_name =
                        FStarC_TypeChecker_Env.norm_eff_name
                          cfg.FStarC_TypeChecker_Cfg.tcenv m in
                      let ed =
                        FStarC_TypeChecker_Env.get_effect_decl
                          cfg.FStarC_TypeChecker_Cfg.tcenv eff_name in
                      let uu___3 =
                        let uu___4 = FStarC_Syntax_Util.get_eff_repr ed in
                        FStarC_Compiler_Util.must uu___4 in
                      (match uu___3 with
                       | (uu___4, repr) ->
                           let uu___5 =
                             let uu___6 = FStarC_Syntax_Util.get_bind_repr ed in
                             FStarC_Compiler_Util.must uu___6 in
                           (match uu___5 with
                            | (uu___6, bind_repr) ->
                                (match lb.FStarC_Syntax_Syntax.lbname with
                                 | FStar_Pervasives.Inr uu___7 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Pervasives.Inl x ->
                                     let is_return e =
                                       let uu___7 =
                                         let uu___8 =
                                           FStarC_Syntax_Subst.compress e in
                                         uu___8.FStarC_Syntax_Syntax.n in
                                       match uu___7 with
                                       | FStarC_Syntax_Syntax.Tm_meta
                                           { FStarC_Syntax_Syntax.tm2 = e1;
                                             FStarC_Syntax_Syntax.meta =
                                               FStarC_Syntax_Syntax.Meta_monadic
                                               (uu___8, uu___9);_}
                                           ->
                                           let uu___10 =
                                             let uu___11 =
                                               FStarC_Syntax_Subst.compress
                                                 e1 in
                                             uu___11.FStarC_Syntax_Syntax.n in
                                           (match uu___10 with
                                            | FStarC_Syntax_Syntax.Tm_meta
                                                {
                                                  FStarC_Syntax_Syntax.tm2 =
                                                    e2;
                                                  FStarC_Syntax_Syntax.meta =
                                                    FStarC_Syntax_Syntax.Meta_monadic_lift
                                                    (uu___11, msrc, uu___12);_}
                                                when
                                                FStarC_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu___13 =
                                                  FStarC_Syntax_Subst.compress
                                                    e2 in
                                                FStar_Pervasives_Native.Some
                                                  uu___13
                                            | uu___11 ->
                                                FStar_Pervasives_Native.None)
                                       | uu___8 ->
                                           FStar_Pervasives_Native.None in
                                     let uu___7 =
                                       is_return
                                         lb.FStarC_Syntax_Syntax.lbdef in
                                     (match uu___7 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            {
                                              FStarC_Syntax_Syntax.lbname =
                                                (lb.FStarC_Syntax_Syntax.lbname);
                                              FStarC_Syntax_Syntax.lbunivs =
                                                (lb.FStarC_Syntax_Syntax.lbunivs);
                                              FStarC_Syntax_Syntax.lbtyp =
                                                (lb.FStarC_Syntax_Syntax.lbtyp);
                                              FStarC_Syntax_Syntax.lbeff =
                                                FStarC_Parser_Const.effect_PURE_lid;
                                              FStarC_Syntax_Syntax.lbdef = e;
                                              FStarC_Syntax_Syntax.lbattrs =
                                                (lb.FStarC_Syntax_Syntax.lbattrs);
                                              FStarC_Syntax_Syntax.lbpos =
                                                (lb.FStarC_Syntax_Syntax.lbpos)
                                            } in
                                          let uu___8 =
                                            FStarC_Compiler_List.tl stack1 in
                                          let uu___9 =
                                            let uu___10 =
                                              let uu___11 =
                                                let uu___12 =
                                                  FStarC_Syntax_Util.mk_reify
                                                    body
                                                    (FStar_Pervasives_Native.Some
                                                       m) in
                                                {
                                                  FStarC_Syntax_Syntax.lbs =
                                                    (false, [lb1]);
                                                  FStarC_Syntax_Syntax.body1
                                                    = uu___12
                                                } in
                                              FStarC_Syntax_Syntax.Tm_let
                                                uu___11 in
                                            FStarC_Syntax_Syntax.mk uu___10
                                              top2.FStarC_Syntax_Syntax.pos in
                                          norm cfg env1 uu___8 uu___9
                                      | FStar_Pervasives_Native.None ->
                                          let uu___8 =
                                            let uu___9 = is_return body in
                                            match uu___9 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStarC_Syntax_Syntax.n =
                                                    FStarC_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStarC_Syntax_Syntax.pos =
                                                    uu___10;
                                                  FStarC_Syntax_Syntax.vars =
                                                    uu___11;
                                                  FStarC_Syntax_Syntax.hash_code
                                                    = uu___12;_}
                                                ->
                                                FStarC_Syntax_Syntax.bv_eq x
                                                  y
                                            | uu___10 -> false in
                                          if uu___8
                                          then
                                            norm cfg env1 stack1
                                              lb.FStarC_Syntax_Syntax.lbdef
                                          else
                                            (let rng =
                                               top2.FStarC_Syntax_Syntax.pos in
                                             let head =
                                               FStarC_Syntax_Util.mk_reify
                                                 lb.FStarC_Syntax_Syntax.lbdef
                                                 (FStar_Pervasives_Native.Some
                                                    m) in
                                             let body1 =
                                               FStarC_Syntax_Util.mk_reify
                                                 body
                                                 (FStar_Pervasives_Native.Some
                                                    m) in
                                             let body_rc =
                                               {
                                                 FStarC_Syntax_Syntax.residual_effect
                                                   = m;
                                                 FStarC_Syntax_Syntax.residual_typ
                                                   =
                                                   (FStar_Pervasives_Native.Some
                                                      t);
                                                 FStarC_Syntax_Syntax.residual_flags
                                                   = []
                                               } in
                                             let body2 =
                                               let uu___10 =
                                                 let uu___11 =
                                                   let uu___12 =
                                                     let uu___13 =
                                                       FStarC_Syntax_Syntax.mk_binder
                                                         x in
                                                     [uu___13] in
                                                   {
                                                     FStarC_Syntax_Syntax.bs
                                                       = uu___12;
                                                     FStarC_Syntax_Syntax.body
                                                       = body1;
                                                     FStarC_Syntax_Syntax.rc_opt
                                                       =
                                                       (FStar_Pervasives_Native.Some
                                                          body_rc)
                                                   } in
                                                 FStarC_Syntax_Syntax.Tm_abs
                                                   uu___11 in
                                               FStarC_Syntax_Syntax.mk
                                                 uu___10
                                                 body1.FStarC_Syntax_Syntax.pos in
                                             let close =
                                               closure_as_term cfg env1 in
                                             let bind_inst =
                                               let uu___10 =
                                                 let uu___11 =
                                                   FStarC_Syntax_Subst.compress
                                                     bind_repr in
                                                 uu___11.FStarC_Syntax_Syntax.n in
                                               match uu___10 with
                                               | FStarC_Syntax_Syntax.Tm_uinst
                                                   (bind,
                                                    uu___11::uu___12::[])
                                                   ->
                                                   let uu___13 =
                                                     let uu___14 =
                                                       let uu___15 =
                                                         let uu___16 =
                                                           let uu___17 =
                                                             close
                                                               lb.FStarC_Syntax_Syntax.lbtyp in
                                                           (cfg.FStarC_TypeChecker_Cfg.tcenv).FStarC_TypeChecker_Env.universe_of
                                                             cfg.FStarC_TypeChecker_Cfg.tcenv
                                                             uu___17 in
                                                         let uu___17 =
                                                           let uu___18 =
                                                             let uu___19 =
                                                               close t in
                                                             (cfg.FStarC_TypeChecker_Cfg.tcenv).FStarC_TypeChecker_Env.universe_of
                                                               cfg.FStarC_TypeChecker_Cfg.tcenv
                                                               uu___19 in
                                                           [uu___18] in
                                                         uu___16 :: uu___17 in
                                                       (bind, uu___15) in
                                                     FStarC_Syntax_Syntax.Tm_uinst
                                                       uu___14 in
                                                   FStarC_Syntax_Syntax.mk
                                                     uu___13 rng
                                               | uu___11 ->
                                                   failwith
                                                     "NIY : Reification of indexed effects" in
                                             let bind_inst_args f_arg =
                                               let uu___10 =
                                                 FStarC_Syntax_Util.is_layered
                                                   ed in
                                               if uu___10
                                               then
                                                 let bind_has_range_args =
                                                   FStarC_Syntax_Util.has_attribute
                                                     ed.FStarC_Syntax_Syntax.eff_attrs
                                                     FStarC_Parser_Const.bind_has_range_args_attr in
                                                 let num_fixed_binders =
                                                   if bind_has_range_args
                                                   then (Prims.of_int (4))
                                                   else (Prims.of_int (2)) in
                                                 let unit_args =
                                                   let uu___11 =
                                                     let uu___12 =
                                                       let uu___13 =
                                                         let uu___14 =
                                                           let uu___15 =
                                                             FStarC_Syntax_Util.get_bind_vc_combinator
                                                               ed in
                                                           FStar_Pervasives_Native.fst
                                                             uu___15 in
                                                         FStar_Pervasives_Native.snd
                                                           uu___14 in
                                                       FStarC_Syntax_Subst.compress
                                                         uu___13 in
                                                     uu___12.FStarC_Syntax_Syntax.n in
                                                   match uu___11 with
                                                   | FStarC_Syntax_Syntax.Tm_arrow
                                                       {
                                                         FStarC_Syntax_Syntax.bs1
                                                           =
                                                           uu___12::uu___13::bs;
                                                         FStarC_Syntax_Syntax.comp
                                                           = uu___14;_}
                                                       when
                                                       (FStarC_Compiler_List.length
                                                          bs)
                                                         >= num_fixed_binders
                                                       ->
                                                       let uu___15 =
                                                         let uu___16 =
                                                           FStarC_Compiler_List.splitAt
                                                             ((FStarC_Compiler_List.length
                                                                 bs)
                                                                -
                                                                num_fixed_binders)
                                                             bs in
                                                         FStar_Pervasives_Native.fst
                                                           uu___16 in
                                                       FStarC_Compiler_List.map
                                                         (fun uu___16 ->
                                                            FStarC_Syntax_Syntax.as_arg
                                                              FStarC_Syntax_Syntax.unit_const)
                                                         uu___15
                                                   | uu___12 ->
                                                       let uu___13 =
                                                         let uu___14 =
                                                           FStarC_Class_Show.show
                                                             FStarC_Ident.showable_lident
                                                             ed.FStarC_Syntax_Syntax.mname in
                                                         let uu___15 =
                                                           FStarC_Class_Show.show
                                                             FStarC_Class_Show.showable_int
                                                             num_fixed_binders in
                                                         let uu___16 =
                                                           let uu___17 =
                                                             let uu___18 =
                                                               let uu___19 =
                                                                 FStarC_Syntax_Util.get_bind_vc_combinator
                                                                   ed in
                                                               FStar_Pervasives_Native.fst
                                                                 uu___19 in
                                                             FStar_Pervasives_Native.snd
                                                               uu___18 in
                                                           FStarC_Class_Show.show
                                                             FStarC_Syntax_Print.showable_term
                                                             uu___17 in
                                                         FStarC_Compiler_Util.format3
                                                           "bind_wp for layered effect %s is not an arrow with >= %s arguments (%s)"
                                                           uu___14 uu___15
                                                           uu___16 in
                                                       FStarC_Errors.raise_error
                                                         FStarC_Class_HasRange.hasRange_range
                                                         rng
                                                         FStarC_Errors_Codes.Fatal_UnexpectedEffect
                                                         ()
                                                         (Obj.magic
                                                            FStarC_Errors_Msg.is_error_message_string)
                                                         (Obj.magic uu___13) in
                                                 let range_args =
                                                   if bind_has_range_args
                                                   then
                                                     let uu___11 =
                                                       let uu___12 =
                                                         FStarC_TypeChecker_Primops_Base.embed_simple
                                                           FStarC_Syntax_Embeddings.e_range
                                                           lb.FStarC_Syntax_Syntax.lbpos
                                                           lb.FStarC_Syntax_Syntax.lbpos in
                                                       FStarC_Syntax_Syntax.as_arg
                                                         uu___12 in
                                                     let uu___12 =
                                                       let uu___13 =
                                                         let uu___14 =
                                                           FStarC_TypeChecker_Primops_Base.embed_simple
                                                             FStarC_Syntax_Embeddings.e_range
                                                             body2.FStarC_Syntax_Syntax.pos
                                                             body2.FStarC_Syntax_Syntax.pos in
                                                         FStarC_Syntax_Syntax.as_arg
                                                           uu___14 in
                                                       [uu___13] in
                                                     uu___11 :: uu___12
                                                   else [] in
                                                 let uu___11 =
                                                   FStarC_Syntax_Syntax.as_arg
                                                     lb.FStarC_Syntax_Syntax.lbtyp in
                                                 let uu___12 =
                                                   let uu___13 =
                                                     FStarC_Syntax_Syntax.as_arg
                                                       t in
                                                   let uu___14 =
                                                     let uu___15 =
                                                       let uu___16 =
                                                         let uu___17 =
                                                           FStarC_Syntax_Syntax.as_arg
                                                             f_arg in
                                                         let uu___18 =
                                                           let uu___19 =
                                                             FStarC_Syntax_Syntax.as_arg
                                                               body2 in
                                                           [uu___19] in
                                                         uu___17 :: uu___18 in
                                                       FStarC_Compiler_List.op_At
                                                         range_args uu___16 in
                                                     FStarC_Compiler_List.op_At
                                                       unit_args uu___15 in
                                                   uu___13 :: uu___14 in
                                                 uu___11 :: uu___12
                                               else
                                                 (let maybe_range_arg =
                                                    let uu___12 =
                                                      FStarC_Compiler_Util.for_some
                                                        (FStarC_TypeChecker_TermEqAndSimplify.eq_tm_bool
                                                           cfg.FStarC_TypeChecker_Cfg.tcenv
                                                           FStarC_Syntax_Util.dm4f_bind_range_attr)
                                                        ed.FStarC_Syntax_Syntax.eff_attrs in
                                                    if uu___12
                                                    then
                                                      let uu___13 =
                                                        let uu___14 =
                                                          FStarC_TypeChecker_Primops_Base.embed_simple
                                                            FStarC_Syntax_Embeddings.e_range
                                                            lb.FStarC_Syntax_Syntax.lbpos
                                                            lb.FStarC_Syntax_Syntax.lbpos in
                                                        FStarC_Syntax_Syntax.as_arg
                                                          uu___14 in
                                                      let uu___14 =
                                                        let uu___15 =
                                                          let uu___16 =
                                                            FStarC_TypeChecker_Primops_Base.embed_simple
                                                              FStarC_Syntax_Embeddings.e_range
                                                              body2.FStarC_Syntax_Syntax.pos
                                                              body2.FStarC_Syntax_Syntax.pos in
                                                          FStarC_Syntax_Syntax.as_arg
                                                            uu___16 in
                                                        [uu___15] in
                                                      uu___13 :: uu___14
                                                    else [] in
                                                  let uu___12 =
                                                    let uu___13 =
                                                      FStarC_Syntax_Syntax.as_arg
                                                        lb.FStarC_Syntax_Syntax.lbtyp in
                                                    let uu___14 =
                                                      let uu___15 =
                                                        FStarC_Syntax_Syntax.as_arg
                                                          t in
                                                      [uu___15] in
                                                    uu___13 :: uu___14 in
                                                  let uu___13 =
                                                    let uu___14 =
                                                      let uu___15 =
                                                        FStarC_Syntax_Syntax.as_arg
                                                          FStarC_Syntax_Syntax.tun in
                                                      let uu___16 =
                                                        let uu___17 =
                                                          FStarC_Syntax_Syntax.as_arg
                                                            f_arg in
                                                        let uu___18 =
                                                          let uu___19 =
                                                            FStarC_Syntax_Syntax.as_arg
                                                              FStarC_Syntax_Syntax.tun in
                                                          let uu___20 =
                                                            let uu___21 =
                                                              FStarC_Syntax_Syntax.as_arg
                                                                body2 in
                                                            [uu___21] in
                                                          uu___19 :: uu___20 in
                                                        uu___17 :: uu___18 in
                                                      uu___15 :: uu___16 in
                                                    FStarC_Compiler_List.op_At
                                                      maybe_range_arg uu___14 in
                                                  FStarC_Compiler_List.op_At
                                                    uu___12 uu___13) in
                                             let reified =
                                               let is_total_effect =
                                                 FStarC_TypeChecker_Env.is_total_effect
                                                   cfg.FStarC_TypeChecker_Cfg.tcenv
                                                   eff_name in
                                               if is_total_effect
                                               then
                                                 let uu___10 =
                                                   let uu___11 =
                                                     let uu___12 =
                                                       bind_inst_args head in
                                                     {
                                                       FStarC_Syntax_Syntax.hd
                                                         = bind_inst;
                                                       FStarC_Syntax_Syntax.args
                                                         = uu___12
                                                     } in
                                                   FStarC_Syntax_Syntax.Tm_app
                                                     uu___11 in
                                                 FStarC_Syntax_Syntax.mk
                                                   uu___10 rng
                                               else
                                                 (let uu___11 =
                                                    let bv =
                                                      FStarC_Syntax_Syntax.new_bv
                                                        FStar_Pervasives_Native.None
                                                        x.FStarC_Syntax_Syntax.sort in
                                                    let lb1 =
                                                      let uu___12 =
                                                        let uu___13 =
                                                          let uu___14 =
                                                            FStarC_Syntax_Syntax.as_arg
                                                              x.FStarC_Syntax_Syntax.sort in
                                                          [uu___14] in
                                                        FStarC_Syntax_Util.mk_app
                                                          repr uu___13 in
                                                      {
                                                        FStarC_Syntax_Syntax.lbname
                                                          =
                                                          (FStar_Pervasives.Inl
                                                             bv);
                                                        FStarC_Syntax_Syntax.lbunivs
                                                          = [];
                                                        FStarC_Syntax_Syntax.lbtyp
                                                          = uu___12;
                                                        FStarC_Syntax_Syntax.lbeff
                                                          =
                                                          (if is_total_effect
                                                           then
                                                             FStarC_Parser_Const.effect_Tot_lid
                                                           else
                                                             FStarC_Parser_Const.effect_Dv_lid);
                                                        FStarC_Syntax_Syntax.lbdef
                                                          = head;
                                                        FStarC_Syntax_Syntax.lbattrs
                                                          = [];
                                                        FStarC_Syntax_Syntax.lbpos
                                                          =
                                                          (head.FStarC_Syntax_Syntax.pos)
                                                      } in
                                                    let uu___12 =
                                                      FStarC_Syntax_Syntax.bv_to_name
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
                                                                FStarC_Syntax_Syntax.mk_binder
                                                                  head_bv in
                                                              [uu___16] in
                                                            let uu___16 =
                                                              let uu___17 =
                                                                let uu___18 =
                                                                  let uu___19
                                                                    =
                                                                    bind_inst_args
                                                                    head1 in
                                                                  {
                                                                    FStarC_Syntax_Syntax.hd
                                                                    =
                                                                    bind_inst;
                                                                    FStarC_Syntax_Syntax.args
                                                                    = uu___19
                                                                  } in
                                                                FStarC_Syntax_Syntax.Tm_app
                                                                  uu___18 in
                                                              FStarC_Syntax_Syntax.mk
                                                                uu___17 rng in
                                                            FStarC_Syntax_Subst.close
                                                              uu___15 uu___16 in
                                                          {
                                                            FStarC_Syntax_Syntax.lbs
                                                              =
                                                              (false,
                                                                [lb_head]);
                                                            FStarC_Syntax_Syntax.body1
                                                              = uu___14
                                                          } in
                                                        FStarC_Syntax_Syntax.Tm_let
                                                          uu___13 in
                                                      FStarC_Syntax_Syntax.mk
                                                        uu___12 rng) in
                                             FStarC_TypeChecker_Cfg.log cfg
                                               (fun uu___11 ->
                                                  let uu___12 =
                                                    FStarC_Class_Show.show
                                                      FStarC_Syntax_Print.showable_term
                                                      top0 in
                                                  let uu___13 =
                                                    FStarC_Class_Show.show
                                                      FStarC_Syntax_Print.showable_term
                                                      reified in
                                                  FStarC_Compiler_Util.print2
                                                    "Reified (1) <%s> to %s\n"
                                                    uu___12 uu___13);
                                             (let uu___11 =
                                                FStarC_Compiler_List.tl
                                                  stack1 in
                                              norm cfg env1 uu___11 reified))))))
                  | FStarC_Syntax_Syntax.Tm_app
                      { FStarC_Syntax_Syntax.hd = head;
                        FStarC_Syntax_Syntax.args = args;_}
                      ->
                      ((let uu___4 = FStarC_Options.defensive () in
                        if uu___4
                        then
                          let is_arg_impure uu___5 =
                            match uu___5 with
                            | (e, q) ->
                                let uu___6 =
                                  let uu___7 = FStarC_Syntax_Subst.compress e in
                                  uu___7.FStarC_Syntax_Syntax.n in
                                (match uu___6 with
                                 | FStarC_Syntax_Syntax.Tm_meta
                                     { FStarC_Syntax_Syntax.tm2 = e0;
                                       FStarC_Syntax_Syntax.meta =
                                         FStarC_Syntax_Syntax.Meta_monadic_lift
                                         (m1, m2, t');_}
                                     ->
                                     let uu___7 =
                                       FStarC_Syntax_Util.is_pure_effect m1 in
                                     Prims.op_Negation uu___7
                                 | uu___7 -> false) in
                          let uu___5 =
                            let uu___6 =
                              let uu___7 = FStarC_Syntax_Syntax.as_arg head in
                              uu___7 :: args in
                            FStarC_Compiler_Util.for_some is_arg_impure
                              uu___6 in
                          (if uu___5
                           then
                             let uu___6 =
                               let uu___7 =
                                 FStarC_Class_Show.show
                                   FStarC_Syntax_Print.showable_term top2 in
                               FStarC_Compiler_Util.format1
                                 "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                 uu___7 in
                             FStarC_Errors.log_issue
                               (FStarC_Syntax_Syntax.has_range_syntax ())
                               top2 FStarC_Errors_Codes.Warning_Defensive ()
                               (Obj.magic
                                  FStarC_Errors_Msg.is_error_message_string)
                               (Obj.magic uu___6)
                           else ())
                        else ());
                       (let fallback1 uu___4 =
                          FStarC_TypeChecker_Cfg.log cfg
                            (fun uu___6 ->
                               let uu___7 =
                                 FStarC_Class_Show.show
                                   FStarC_Syntax_Print.showable_term top0 in
                               FStarC_Compiler_Util.print2
                                 "Reified (2) <%s> to %s\n" uu___7 "");
                          (let uu___6 = FStarC_Compiler_List.tl stack1 in
                           let uu___7 =
                             FStarC_Syntax_Util.mk_reify top2
                               (FStar_Pervasives_Native.Some m) in
                           norm cfg env1 uu___6 uu___7) in
                        let fallback2 uu___4 =
                          FStarC_TypeChecker_Cfg.log cfg
                            (fun uu___6 ->
                               let uu___7 =
                                 FStarC_Class_Show.show
                                   FStarC_Syntax_Print.showable_term top0 in
                               FStarC_Compiler_Util.print2
                                 "Reified (3) <%s> to %s\n" uu___7 "");
                          (let uu___6 = FStarC_Compiler_List.tl stack1 in
                           let uu___7 =
                             FStarC_Syntax_Syntax.mk
                               (FStarC_Syntax_Syntax.Tm_meta
                                  {
                                    FStarC_Syntax_Syntax.tm2 = top2;
                                    FStarC_Syntax_Syntax.meta =
                                      (FStarC_Syntax_Syntax.Meta_monadic
                                         (m, t))
                                  }) top0.FStarC_Syntax_Syntax.pos in
                           norm cfg env1 uu___6 uu___7) in
                        let uu___4 =
                          let uu___5 = FStarC_Syntax_Util.un_uinst head in
                          uu___5.FStarC_Syntax_Syntax.n in
                        match uu___4 with
                        | FStarC_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStarC_Syntax_Syntax.lid_of_fv fv in
                            let qninfo =
                              FStarC_TypeChecker_Env.lookup_qname
                                cfg.FStarC_TypeChecker_Cfg.tcenv lid in
                            let uu___5 =
                              let uu___6 =
                                FStarC_TypeChecker_Env.is_action
                                  cfg.FStarC_TypeChecker_Cfg.tcenv lid in
                              Prims.op_Negation uu___6 in
                            if uu___5
                            then fallback1 ()
                            else
                              (let uu___7 =
                                 let uu___8 =
                                   FStarC_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStarC_TypeChecker_Cfg.delta_level
                                     (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
                                     qninfo in
                                 FStarC_Compiler_Option.isNone uu___8 in
                               if uu___7
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu___9 =
                                      FStarC_Syntax_Util.mk_reify head
                                        (FStar_Pervasives_Native.Some m) in
                                    FStarC_Syntax_Syntax.mk_Tm_app uu___9
                                      args t.FStarC_Syntax_Syntax.pos in
                                  let uu___9 = FStarC_Compiler_List.tl stack1 in
                                  norm cfg env1 uu___9 t1))
                        | uu___5 -> fallback1 ()))
                  | FStarC_Syntax_Syntax.Tm_meta
                      { FStarC_Syntax_Syntax.tm2 = e;
                        FStarC_Syntax_Syntax.meta =
                          FStarC_Syntax_Syntax.Meta_monadic uu___3;_}
                      -> do_reify_monadic fallback cfg env1 stack1 e m t
                  | FStarC_Syntax_Syntax.Tm_meta
                      { FStarC_Syntax_Syntax.tm2 = e;
                        FStarC_Syntax_Syntax.meta =
                          FStarC_Syntax_Syntax.Meta_monadic_lift
                          (msrc, mtgt, t');_}
                      ->
                      let lifted =
                        let uu___3 = closure_as_term cfg env1 t' in
                        reify_lift cfg e msrc mtgt uu___3 in
                      (FStarC_TypeChecker_Cfg.log cfg
                         (fun uu___4 ->
                            let uu___5 =
                              FStarC_Class_Show.show
                                FStarC_Syntax_Print.showable_term lifted in
                            FStarC_Compiler_Util.print1
                              "Reified lift to (2): %s\n" uu___5);
                       (let uu___4 = FStarC_Compiler_List.tl stack1 in
                        norm cfg env1 uu___4 lifted))
                  | FStarC_Syntax_Syntax.Tm_match
                      { FStarC_Syntax_Syntax.scrutinee = e;
                        FStarC_Syntax_Syntax.ret_opt = asc_opt;
                        FStarC_Syntax_Syntax.brs = branches1;
                        FStarC_Syntax_Syntax.rc_opt1 = lopt;_}
                      ->
                      let branches2 =
                        FStarC_Compiler_List.map
                          (fun uu___3 ->
                             match uu___3 with
                             | (pat, wopt, tm) ->
                                 let uu___4 =
                                   FStarC_Syntax_Util.mk_reify tm
                                     (FStar_Pervasives_Native.Some m) in
                                 (pat, wopt, uu___4)) branches1 in
                      let tm =
                        FStarC_Syntax_Syntax.mk
                          (FStarC_Syntax_Syntax.Tm_match
                             {
                               FStarC_Syntax_Syntax.scrutinee = e;
                               FStarC_Syntax_Syntax.ret_opt = asc_opt;
                               FStarC_Syntax_Syntax.brs = branches2;
                               FStarC_Syntax_Syntax.rc_opt1 = lopt
                             }) top2.FStarC_Syntax_Syntax.pos in
                      let uu___3 = FStarC_Compiler_List.tl stack1 in
                      norm cfg env1 uu___3 tm
                  | uu___3 -> fallback ()))
and (reify_lift :
  FStarC_TypeChecker_Cfg.cfg ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.monad_name ->
        FStarC_Syntax_Syntax.monad_name ->
          FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun cfg ->
    fun e ->
      fun msrc ->
        fun mtgt ->
          fun t ->
            let env1 = cfg.FStarC_TypeChecker_Cfg.tcenv in
            FStarC_TypeChecker_Cfg.log cfg
              (fun uu___1 ->
                 let uu___2 = FStarC_Ident.string_of_lid msrc in
                 let uu___3 = FStarC_Ident.string_of_lid mtgt in
                 let uu___4 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
                 FStarC_Compiler_Util.print3 "Reifying lift %s -> %s: %s\n"
                   uu___2 uu___3 uu___4);
            (let uu___1 =
               ((FStarC_Syntax_Util.is_pure_effect msrc) ||
                  (FStarC_Syntax_Util.is_div_effect msrc))
                 &&
                 (let uu___2 =
                    FStarC_TypeChecker_Env.is_layered_effect env1 mtgt in
                  Prims.op_Negation uu___2) in
             if uu___1
             then
               let ed =
                 let uu___2 =
                   FStarC_TypeChecker_Env.norm_eff_name
                     cfg.FStarC_TypeChecker_Cfg.tcenv mtgt in
                 FStarC_TypeChecker_Env.get_effect_decl env1 uu___2 in
               let uu___2 =
                 let uu___3 = FStarC_Syntax_Util.get_eff_repr ed in
                 FStarC_Compiler_Util.must uu___3 in
               match uu___2 with
               | (uu___3, repr) ->
                   let uu___4 =
                     let uu___5 = FStarC_Syntax_Util.get_return_repr ed in
                     FStarC_Compiler_Util.must uu___5 in
                   (match uu___4 with
                    | (uu___5, return_repr) ->
                        let return_inst =
                          let uu___6 =
                            let uu___7 =
                              FStarC_Syntax_Subst.compress return_repr in
                            uu___7.FStarC_Syntax_Syntax.n in
                          match uu___6 with
                          | FStarC_Syntax_Syntax.Tm_uinst
                              (return_tm, uu___7::[]) ->
                              let uu___8 =
                                let uu___9 =
                                  let uu___10 =
                                    let uu___11 =
                                      env1.FStarC_TypeChecker_Env.universe_of
                                        env1 t in
                                    [uu___11] in
                                  (return_tm, uu___10) in
                                FStarC_Syntax_Syntax.Tm_uinst uu___9 in
                              FStarC_Syntax_Syntax.mk uu___8
                                e.FStarC_Syntax_Syntax.pos
                          | uu___7 ->
                              failwith "NIY : Reification of indexed effects" in
                        let uu___6 =
                          let bv =
                            FStarC_Syntax_Syntax.new_bv
                              FStar_Pervasives_Native.None t in
                          let lb =
                            let uu___7 =
                              let uu___8 =
                                let uu___9 = FStarC_Syntax_Syntax.as_arg t in
                                [uu___9] in
                              FStarC_Syntax_Util.mk_app repr uu___8 in
                            {
                              FStarC_Syntax_Syntax.lbname =
                                (FStar_Pervasives.Inl bv);
                              FStarC_Syntax_Syntax.lbunivs = [];
                              FStarC_Syntax_Syntax.lbtyp = uu___7;
                              FStarC_Syntax_Syntax.lbeff = msrc;
                              FStarC_Syntax_Syntax.lbdef = e;
                              FStarC_Syntax_Syntax.lbattrs = [];
                              FStarC_Syntax_Syntax.lbpos =
                                (e.FStarC_Syntax_Syntax.pos)
                            } in
                          let uu___7 = FStarC_Syntax_Syntax.bv_to_name bv in
                          (lb, bv, uu___7) in
                        (match uu___6 with
                         | (lb_e, e_bv, e1) ->
                             let uu___7 =
                               let uu___8 =
                                 let uu___9 =
                                   let uu___10 =
                                     let uu___11 =
                                       FStarC_Syntax_Syntax.mk_binder e_bv in
                                     [uu___11] in
                                   let uu___11 =
                                     let uu___12 =
                                       let uu___13 =
                                         let uu___14 =
                                           let uu___15 =
                                             FStarC_Syntax_Syntax.as_arg t in
                                           let uu___16 =
                                             let uu___17 =
                                               FStarC_Syntax_Syntax.as_arg e1 in
                                             [uu___17] in
                                           uu___15 :: uu___16 in
                                         {
                                           FStarC_Syntax_Syntax.hd =
                                             return_inst;
                                           FStarC_Syntax_Syntax.args =
                                             uu___14
                                         } in
                                       FStarC_Syntax_Syntax.Tm_app uu___13 in
                                     FStarC_Syntax_Syntax.mk uu___12
                                       e1.FStarC_Syntax_Syntax.pos in
                                   FStarC_Syntax_Subst.close uu___10 uu___11 in
                                 {
                                   FStarC_Syntax_Syntax.lbs = (false, [lb_e]);
                                   FStarC_Syntax_Syntax.body1 = uu___9
                                 } in
                               FStarC_Syntax_Syntax.Tm_let uu___8 in
                             FStarC_Syntax_Syntax.mk uu___7
                               e1.FStarC_Syntax_Syntax.pos))
             else
               (let uu___3 = FStarC_TypeChecker_Env.monad_leq env1 msrc mtgt in
                match uu___3 with
                | FStar_Pervasives_Native.None ->
                    let uu___4 =
                      let uu___5 = FStarC_Ident.string_of_lid msrc in
                      let uu___6 = FStarC_Ident.string_of_lid mtgt in
                      FStarC_Compiler_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu___5 uu___6 in
                    failwith uu___4
                | FStar_Pervasives_Native.Some
                    { FStarC_TypeChecker_Env.msource = uu___4;
                      FStarC_TypeChecker_Env.mtarget = uu___5;
                      FStarC_TypeChecker_Env.mlift =
                        { FStarC_TypeChecker_Env.mlift_wp = uu___6;
                          FStarC_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None;_};
                      FStarC_TypeChecker_Env.mpath = uu___7;_}
                    ->
                    let uu___8 =
                      let uu___9 = FStarC_Ident.string_of_lid msrc in
                      let uu___10 = FStarC_Ident.string_of_lid mtgt in
                      FStarC_Compiler_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu___9 uu___10 in
                    failwith uu___8
                | FStar_Pervasives_Native.Some
                    { FStarC_TypeChecker_Env.msource = uu___4;
                      FStarC_TypeChecker_Env.mtarget = uu___5;
                      FStarC_TypeChecker_Env.mlift =
                        { FStarC_TypeChecker_Env.mlift_wp = uu___6;
                          FStarC_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};
                      FStarC_TypeChecker_Env.mpath = uu___7;_}
                    ->
                    let e1 =
                      let uu___8 =
                        FStarC_TypeChecker_Env.is_reifiable_effect env1 msrc in
                      if uu___8
                      then
                        FStarC_Syntax_Util.mk_reify e
                          (FStar_Pervasives_Native.Some msrc)
                      else
                        (let uu___10 =
                           let uu___11 =
                             let uu___12 =
                               let uu___13 =
                                 FStarC_Syntax_Syntax.null_binder
                                   FStarC_Syntax_Syntax.t_unit in
                               [uu___13] in
                             {
                               FStarC_Syntax_Syntax.bs = uu___12;
                               FStarC_Syntax_Syntax.body = e;
                               FStarC_Syntax_Syntax.rc_opt =
                                 (FStar_Pervasives_Native.Some
                                    {
                                      FStarC_Syntax_Syntax.residual_effect =
                                        msrc;
                                      FStarC_Syntax_Syntax.residual_typ =
                                        (FStar_Pervasives_Native.Some t);
                                      FStarC_Syntax_Syntax.residual_flags =
                                        []
                                    })
                             } in
                           FStarC_Syntax_Syntax.Tm_abs uu___11 in
                         FStarC_Syntax_Syntax.mk uu___10
                           e.FStarC_Syntax_Syntax.pos) in
                    let uu___8 =
                      env1.FStarC_TypeChecker_Env.universe_of env1 t in
                    lift uu___8 t e1))
and (norm_pattern_args :
  FStarC_TypeChecker_Cfg.cfg ->
    env ->
      (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
        FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list Prims.list ->
        (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
          FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
          Prims.list Prims.list)
  =
  fun cfg ->
    fun env1 ->
      fun args ->
        FStarC_Compiler_List.map
          (FStarC_Compiler_List.map
             (fun uu___ ->
                match uu___ with
                | (a, imp) ->
                    let uu___1 = norm cfg env1 [] a in (uu___1, imp))) args
and (norm_comp :
  FStarC_TypeChecker_Cfg.cfg ->
    env -> FStarC_Syntax_Syntax.comp -> FStarC_Syntax_Syntax.comp)
  =
  fun cfg ->
    fun env1 ->
      fun comp ->
        FStarC_TypeChecker_Cfg.log cfg
          (fun uu___1 ->
             let uu___2 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_comp comp in
             let uu___3 =
               FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                 (FStarC_Compiler_List.length env1) in
             FStarC_Compiler_Util.print2
               ">>> %s\nNormComp with with %s env elements\n" uu___2 uu___3);
        (match comp.FStarC_Syntax_Syntax.n with
         | FStarC_Syntax_Syntax.Total t ->
             let t1 = norm cfg env1 [] t in
             let uu___1 = FStarC_Syntax_Syntax.mk_Total t1 in
             {
               FStarC_Syntax_Syntax.n = (uu___1.FStarC_Syntax_Syntax.n);
               FStarC_Syntax_Syntax.pos = (comp.FStarC_Syntax_Syntax.pos);
               FStarC_Syntax_Syntax.vars = (uu___1.FStarC_Syntax_Syntax.vars);
               FStarC_Syntax_Syntax.hash_code =
                 (uu___1.FStarC_Syntax_Syntax.hash_code)
             }
         | FStarC_Syntax_Syntax.GTotal t ->
             let t1 = norm cfg env1 [] t in
             let uu___1 = FStarC_Syntax_Syntax.mk_GTotal t1 in
             {
               FStarC_Syntax_Syntax.n = (uu___1.FStarC_Syntax_Syntax.n);
               FStarC_Syntax_Syntax.pos = (comp.FStarC_Syntax_Syntax.pos);
               FStarC_Syntax_Syntax.vars = (uu___1.FStarC_Syntax_Syntax.vars);
               FStarC_Syntax_Syntax.hash_code =
                 (uu___1.FStarC_Syntax_Syntax.hash_code)
             }
         | FStarC_Syntax_Syntax.Comp ct ->
             let effect_args =
               let uu___1 =
                 let uu___2 =
                   (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
                     &&
                     (let uu___3 =
                        let uu___4 =
                          get_extraction_mode
                            cfg.FStarC_TypeChecker_Cfg.tcenv
                            ct.FStarC_Syntax_Syntax.effect_name in
                        uu___4 = FStarC_Syntax_Syntax.Extract_reify in
                      Prims.op_Negation uu___3) in
                 if uu___2
                 then
                   FStarC_Compiler_List.map
                     (fun uu___3 ->
                        FStarC_Syntax_Syntax.as_arg
                          FStarC_Syntax_Syntax.unit_const)
                 else
                   FStarC_Compiler_List.mapi
                     (fun idx ->
                        fun uu___4 ->
                          match uu___4 with
                          | (a, i) ->
                              let uu___5 = norm cfg env1 [] a in (uu___5, i)) in
               uu___1 ct.FStarC_Syntax_Syntax.effect_args in
             let flags =
               FStarC_Compiler_List.map
                 (fun uu___1 ->
                    match uu___1 with
                    | FStarC_Syntax_Syntax.DECREASES
                        (FStarC_Syntax_Syntax.Decreases_lex l) ->
                        let uu___2 =
                          let uu___3 =
                            FStarC_Compiler_List.map (norm cfg env1 []) l in
                          FStarC_Syntax_Syntax.Decreases_lex uu___3 in
                        FStarC_Syntax_Syntax.DECREASES uu___2
                    | FStarC_Syntax_Syntax.DECREASES
                        (FStarC_Syntax_Syntax.Decreases_wf (rel, e)) ->
                        let uu___2 =
                          let uu___3 =
                            let uu___4 = norm cfg env1 [] rel in
                            let uu___5 = norm cfg env1 [] e in
                            (uu___4, uu___5) in
                          FStarC_Syntax_Syntax.Decreases_wf uu___3 in
                        FStarC_Syntax_Syntax.DECREASES uu___2
                    | f -> f) ct.FStarC_Syntax_Syntax.flags in
             let comp_univs =
               FStarC_Compiler_List.map (norm_universe cfg env1)
                 ct.FStarC_Syntax_Syntax.comp_univs in
             let result_typ =
               norm cfg env1 [] ct.FStarC_Syntax_Syntax.result_typ in
             let uu___1 =
               FStarC_Syntax_Syntax.mk_Comp
                 {
                   FStarC_Syntax_Syntax.comp_univs = comp_univs;
                   FStarC_Syntax_Syntax.effect_name =
                     (ct.FStarC_Syntax_Syntax.effect_name);
                   FStarC_Syntax_Syntax.result_typ = result_typ;
                   FStarC_Syntax_Syntax.effect_args = effect_args;
                   FStarC_Syntax_Syntax.flags = flags
                 } in
             {
               FStarC_Syntax_Syntax.n = (uu___1.FStarC_Syntax_Syntax.n);
               FStarC_Syntax_Syntax.pos = (comp.FStarC_Syntax_Syntax.pos);
               FStarC_Syntax_Syntax.vars = (uu___1.FStarC_Syntax_Syntax.vars);
               FStarC_Syntax_Syntax.hash_code =
                 (uu___1.FStarC_Syntax_Syntax.hash_code)
             })
and (norm_binder :
  FStarC_TypeChecker_Cfg.cfg ->
    env -> FStarC_Syntax_Syntax.binder -> FStarC_Syntax_Syntax.binder)
  =
  fun cfg ->
    fun env1 ->
      fun b ->
        let x =
          let uu___ = b.FStarC_Syntax_Syntax.binder_bv in
          let uu___1 =
            norm cfg env1 []
              (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
          {
            FStarC_Syntax_Syntax.ppname = (uu___.FStarC_Syntax_Syntax.ppname);
            FStarC_Syntax_Syntax.index = (uu___.FStarC_Syntax_Syntax.index);
            FStarC_Syntax_Syntax.sort = uu___1
          } in
        let imp =
          match b.FStarC_Syntax_Syntax.binder_qual with
          | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta t) ->
              let uu___ =
                let uu___1 = closure_as_term cfg env1 t in
                FStarC_Syntax_Syntax.Meta uu___1 in
              FStar_Pervasives_Native.Some uu___
          | i -> i in
        let attrs =
          FStarC_Compiler_List.map (norm cfg env1 [])
            b.FStarC_Syntax_Syntax.binder_attrs in
        FStarC_Syntax_Syntax.mk_binder_with_attrs x imp
          b.FStarC_Syntax_Syntax.binder_positivity attrs
and (norm_binders :
  FStarC_TypeChecker_Cfg.cfg ->
    env -> FStarC_Syntax_Syntax.binders -> FStarC_Syntax_Syntax.binders)
  =
  fun cfg ->
    fun env1 ->
      fun bs ->
        let uu___ =
          FStarC_Compiler_List.fold_left
            (fun uu___1 ->
               fun b ->
                 match uu___1 with
                 | (nbs', env2) ->
                     let b1 = norm_binder cfg env2 b in
                     let uu___2 = let uu___3 = dummy () in uu___3 :: env2 in
                     ((b1 :: nbs'), uu___2)) ([], env1) bs in
        match uu___ with | (nbs, uu___1) -> FStarC_Compiler_List.rev nbs
and (maybe_simplify :
  FStarC_TypeChecker_Cfg.cfg ->
    env ->
      stack ->
        FStarC_Syntax_Syntax.term -> (FStarC_Syntax_Syntax.term * Prims.bool))
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun tm ->
          let uu___ = maybe_simplify_aux cfg env1 stack1 tm in
          match uu___ with
          | (tm', renorm) ->
              (if
                 (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.b380
               then
                 (let uu___2 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                      tm in
                  let uu___3 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                      tm' in
                  let uu___4 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_bool
                      renorm in
                  FStarC_Compiler_Util.print4
                    "%sSimplified\n\t%s to\n\t%s\nrenorm = %s\n"
                    (if
                       (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.simplify
                     then ""
                     else "NOT ") uu___2 uu___3 uu___4)
               else ();
               (tm', renorm))
and (norm_cb :
  FStarC_TypeChecker_Cfg.cfg -> FStarC_Syntax_Embeddings_Base.norm_cb) =
  fun cfg ->
    fun uu___ ->
      match uu___ with
      | FStar_Pervasives.Inr x -> norm cfg [] [] x
      | FStar_Pervasives.Inl l ->
          let uu___1 =
            FStarC_Syntax_DsEnv.try_lookup_lid
              (cfg.FStarC_TypeChecker_Cfg.tcenv).FStarC_TypeChecker_Env.dsenv
              l in
          (match uu___1 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None ->
               let uu___2 =
                 FStarC_Syntax_Syntax.lid_as_fv l
                   FStar_Pervasives_Native.None in
               FStarC_Syntax_Syntax.fv_to_tm uu___2)
and (maybe_simplify_aux :
  FStarC_TypeChecker_Cfg.cfg ->
    env ->
      stack ->
        FStarC_Syntax_Syntax.term -> (FStarC_Syntax_Syntax.term * Prims.bool))
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun tm ->
          let uu___ =
            let uu___1 = norm_cb cfg in reduce_primops uu___1 cfg env1 tm in
          match uu___ with
          | (tm1, renorm) ->
              if
                Prims.op_Negation
                  (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.simplify
              then (tm1, renorm)
              else
                (let w t =
                   {
                     FStarC_Syntax_Syntax.n = (t.FStarC_Syntax_Syntax.n);
                     FStarC_Syntax_Syntax.pos =
                       (tm1.FStarC_Syntax_Syntax.pos);
                     FStarC_Syntax_Syntax.vars =
                       (t.FStarC_Syntax_Syntax.vars);
                     FStarC_Syntax_Syntax.hash_code =
                       (t.FStarC_Syntax_Syntax.hash_code)
                   } in
                 let simp_t t =
                   let uu___2 =
                     let uu___3 = FStarC_Syntax_Util.unmeta t in
                     uu___3.FStarC_Syntax_Syntax.n in
                   match uu___2 with
                   | FStarC_Syntax_Syntax.Tm_fvar fv when
                       FStarC_Syntax_Syntax.fv_eq_lid fv
                         FStarC_Parser_Const.true_lid
                       -> FStar_Pervasives_Native.Some true
                   | FStarC_Syntax_Syntax.Tm_fvar fv when
                       FStarC_Syntax_Syntax.fv_eq_lid fv
                         FStarC_Parser_Const.false_lid
                       -> FStar_Pervasives_Native.Some false
                   | uu___3 -> FStar_Pervasives_Native.None in
                 let is_const_match phi =
                   let uu___2 =
                     let uu___3 = FStarC_Syntax_Subst.compress phi in
                     uu___3.FStarC_Syntax_Syntax.n in
                   match uu___2 with
                   | FStarC_Syntax_Syntax.Tm_match
                       { FStarC_Syntax_Syntax.scrutinee = uu___3;
                         FStarC_Syntax_Syntax.ret_opt = uu___4;
                         FStarC_Syntax_Syntax.brs = br::brs;
                         FStarC_Syntax_Syntax.rc_opt1 = uu___5;_}
                       ->
                       let uu___6 = br in
                       (match uu___6 with
                        | (uu___7, uu___8, e) ->
                            let r =
                              let uu___9 = simp_t e in
                              match uu___9 with
                              | FStar_Pervasives_Native.None ->
                                  FStar_Pervasives_Native.None
                              | FStar_Pervasives_Native.Some b ->
                                  let uu___10 =
                                    FStarC_Compiler_List.for_all
                                      (fun uu___11 ->
                                         match uu___11 with
                                         | (uu___12, uu___13, e') ->
                                             let uu___14 = simp_t e' in
                                             uu___14 =
                                               (FStar_Pervasives_Native.Some
                                                  b)) brs in
                                  if uu___10
                                  then FStar_Pervasives_Native.Some b
                                  else FStar_Pervasives_Native.None in
                            r)
                   | uu___3 -> FStar_Pervasives_Native.None in
                 let maybe_auto_squash t =
                   let uu___2 = FStarC_Syntax_Util.is_sub_singleton t in
                   if uu___2
                   then t
                   else
                     FStarC_Syntax_Util.mk_auto_squash
                       FStarC_Syntax_Syntax.U_zero t in
                 let squashed_head_un_auto_squash_args t =
                   let maybe_un_auto_squash_arg uu___2 =
                     match uu___2 with
                     | (t1, q) ->
                         let uu___3 = FStarC_Syntax_Util.is_auto_squash t1 in
                         (match uu___3 with
                          | FStar_Pervasives_Native.Some
                              (FStarC_Syntax_Syntax.U_zero, t2) -> (t2, q)
                          | uu___4 -> (t1, q)) in
                   let uu___2 = FStarC_Syntax_Util.head_and_args t in
                   match uu___2 with
                   | (head, args) ->
                       let args1 =
                         FStarC_Compiler_List.map maybe_un_auto_squash_arg
                           args in
                       let uu___3 =
                         FStarC_Syntax_Syntax.mk_Tm_app head args1
                           t.FStarC_Syntax_Syntax.pos in
                       (uu___3, false) in
                 let rec clearly_inhabited ty =
                   let uu___2 =
                     let uu___3 = FStarC_Syntax_Util.unmeta ty in
                     uu___3.FStarC_Syntax_Syntax.n in
                   match uu___2 with
                   | FStarC_Syntax_Syntax.Tm_uinst (t, uu___3) ->
                       clearly_inhabited t
                   | FStarC_Syntax_Syntax.Tm_arrow
                       { FStarC_Syntax_Syntax.bs1 = uu___3;
                         FStarC_Syntax_Syntax.comp = c;_}
                       ->
                       clearly_inhabited (FStarC_Syntax_Util.comp_result c)
                   | FStarC_Syntax_Syntax.Tm_fvar fv ->
                       let l = FStarC_Syntax_Syntax.lid_of_fv fv in
                       (((FStarC_Ident.lid_equals l
                            FStarC_Parser_Const.int_lid)
                           ||
                           (FStarC_Ident.lid_equals l
                              FStarC_Parser_Const.bool_lid))
                          ||
                          (FStarC_Ident.lid_equals l
                             FStarC_Parser_Const.string_lid))
                         ||
                         (FStarC_Ident.lid_equals l
                            FStarC_Parser_Const.exn_lid)
                   | uu___3 -> false in
                 let simplify arg =
                   let uu___2 = simp_t (FStar_Pervasives_Native.fst arg) in
                   (uu___2, arg) in
                 let uu___2 = is_forall_const cfg tm1 in
                 match uu___2 with
                 | FStar_Pervasives_Native.Some tm' ->
                     (if
                        (cfg.FStarC_TypeChecker_Cfg.debug).FStarC_TypeChecker_Cfg.wpe
                      then
                        (let uu___4 =
                           FStarC_Class_Show.show
                             FStarC_Syntax_Print.showable_term tm1 in
                         let uu___5 =
                           FStarC_Class_Show.show
                             FStarC_Syntax_Print.showable_term tm' in
                         FStarC_Compiler_Util.print2 "WPE> %s ~> %s\n" uu___4
                           uu___5)
                      else ();
                      (let uu___4 = norm cfg env1 [] tm' in
                       maybe_simplify_aux cfg env1 stack1 uu___4))
                 | FStar_Pervasives_Native.None ->
                     let uu___3 =
                       let uu___4 = FStarC_Syntax_Subst.compress tm1 in
                       uu___4.FStarC_Syntax_Syntax.n in
                     (match uu___3 with
                      | FStarC_Syntax_Syntax.Tm_app
                          {
                            FStarC_Syntax_Syntax.hd =
                              {
                                FStarC_Syntax_Syntax.n =
                                  FStarC_Syntax_Syntax.Tm_uinst
                                  ({
                                     FStarC_Syntax_Syntax.n =
                                       FStarC_Syntax_Syntax.Tm_fvar fv;
                                     FStarC_Syntax_Syntax.pos = uu___4;
                                     FStarC_Syntax_Syntax.vars = uu___5;
                                     FStarC_Syntax_Syntax.hash_code = uu___6;_},
                                   uu___7);
                                FStarC_Syntax_Syntax.pos = uu___8;
                                FStarC_Syntax_Syntax.vars = uu___9;
                                FStarC_Syntax_Syntax.hash_code = uu___10;_};
                            FStarC_Syntax_Syntax.args = args;_}
                          ->
                          let uu___11 =
                            FStarC_Syntax_Syntax.fv_eq_lid fv
                              FStarC_Parser_Const.squash_lid in
                          if uu___11
                          then squashed_head_un_auto_squash_args tm1
                          else
                            (let uu___13 =
                               FStarC_Syntax_Syntax.fv_eq_lid fv
                                 FStarC_Parser_Const.and_lid in
                             if uu___13
                             then
                               let uu___14 =
                                 FStarC_Compiler_List.map simplify args in
                               match uu___14 with
                               | (FStar_Pervasives_Native.Some (true),
                                  uu___15)::(uu___16, (arg, uu___17))::[] ->
                                   let uu___18 = maybe_auto_squash arg in
                                   (uu___18, false)
                               | (uu___15, (arg, uu___16))::(FStar_Pervasives_Native.Some
                                                             (true), uu___17)::[]
                                   ->
                                   let uu___18 = maybe_auto_squash arg in
                                   (uu___18, false)
                               | (FStar_Pervasives_Native.Some (false),
                                  uu___15)::uu___16::[] ->
                                   ((w FStarC_Syntax_Util.t_false), false)
                               | uu___15::(FStar_Pervasives_Native.Some
                                           (false), uu___16)::[]
                                   -> ((w FStarC_Syntax_Util.t_false), false)
                               | uu___15 ->
                                   squashed_head_un_auto_squash_args tm1
                             else
                               (let uu___15 =
                                  FStarC_Syntax_Syntax.fv_eq_lid fv
                                    FStarC_Parser_Const.or_lid in
                                if uu___15
                                then
                                  let uu___16 =
                                    FStarC_Compiler_List.map simplify args in
                                  match uu___16 with
                                  | (FStar_Pervasives_Native.Some (true),
                                     uu___17)::uu___18::[] ->
                                      ((w FStarC_Syntax_Util.t_true), false)
                                  | uu___17::(FStar_Pervasives_Native.Some
                                              (true), uu___18)::[]
                                      ->
                                      ((w FStarC_Syntax_Util.t_true), false)
                                  | (FStar_Pervasives_Native.Some (false),
                                     uu___17)::(uu___18, (arg, uu___19))::[]
                                      ->
                                      let uu___20 = maybe_auto_squash arg in
                                      (uu___20, false)
                                  | (uu___17, (arg, uu___18))::(FStar_Pervasives_Native.Some
                                                                (false),
                                                                uu___19)::[]
                                      ->
                                      let uu___20 = maybe_auto_squash arg in
                                      (uu___20, false)
                                  | uu___17 ->
                                      squashed_head_un_auto_squash_args tm1
                                else
                                  (let uu___17 =
                                     FStarC_Syntax_Syntax.fv_eq_lid fv
                                       FStarC_Parser_Const.imp_lid in
                                   if uu___17
                                   then
                                     let uu___18 =
                                       FStarC_Compiler_List.map simplify args in
                                     match uu___18 with
                                     | uu___19::(FStar_Pervasives_Native.Some
                                                 (true), uu___20)::[]
                                         ->
                                         ((w FStarC_Syntax_Util.t_true),
                                           false)
                                     | (FStar_Pervasives_Native.Some (false),
                                        uu___19)::uu___20::[] ->
                                         ((w FStarC_Syntax_Util.t_true),
                                           false)
                                     | (FStar_Pervasives_Native.Some (true),
                                        uu___19)::(uu___20, (arg, uu___21))::[]
                                         ->
                                         let uu___22 = maybe_auto_squash arg in
                                         (uu___22, false)
                                     | (uu___19, (p, uu___20))::(uu___21,
                                                                 (q, uu___22))::[]
                                         ->
                                         let uu___23 =
                                           FStarC_Syntax_Util.term_eq p q in
                                         (if uu___23
                                          then
                                            ((w FStarC_Syntax_Util.t_true),
                                              false)
                                          else
                                            squashed_head_un_auto_squash_args
                                              tm1)
                                     | uu___19 ->
                                         squashed_head_un_auto_squash_args
                                           tm1
                                   else
                                     (let uu___19 =
                                        FStarC_Syntax_Syntax.fv_eq_lid fv
                                          FStarC_Parser_Const.iff_lid in
                                      if uu___19
                                      then
                                        let uu___20 =
                                          FStarC_Compiler_List.map simplify
                                            args in
                                        match uu___20 with
                                        | (FStar_Pervasives_Native.Some
                                           (true), uu___21)::(FStar_Pervasives_Native.Some
                                                              (true),
                                                              uu___22)::[]
                                            ->
                                            ((w FStarC_Syntax_Util.t_true),
                                              false)
                                        | (FStar_Pervasives_Native.Some
                                           (false), uu___21)::(FStar_Pervasives_Native.Some
                                                               (false),
                                                               uu___22)::[]
                                            ->
                                            ((w FStarC_Syntax_Util.t_true),
                                              false)
                                        | (FStar_Pervasives_Native.Some
                                           (true), uu___21)::(FStar_Pervasives_Native.Some
                                                              (false),
                                                              uu___22)::[]
                                            ->
                                            ((w FStarC_Syntax_Util.t_false),
                                              false)
                                        | (FStar_Pervasives_Native.Some
                                           (false), uu___21)::(FStar_Pervasives_Native.Some
                                                               (true),
                                                               uu___22)::[]
                                            ->
                                            ((w FStarC_Syntax_Util.t_false),
                                              false)
                                        | (uu___21, (arg, uu___22))::
                                            (FStar_Pervasives_Native.Some
                                             (true), uu___23)::[]
                                            ->
                                            let uu___24 =
                                              maybe_auto_squash arg in
                                            (uu___24, false)
                                        | (FStar_Pervasives_Native.Some
                                           (true), uu___21)::(uu___22,
                                                              (arg, uu___23))::[]
                                            ->
                                            let uu___24 =
                                              maybe_auto_squash arg in
                                            (uu___24, false)
                                        | (uu___21, (arg, uu___22))::
                                            (FStar_Pervasives_Native.Some
                                             (false), uu___23)::[]
                                            ->
                                            let uu___24 =
                                              let uu___25 =
                                                FStarC_Syntax_Util.mk_neg arg in
                                              maybe_auto_squash uu___25 in
                                            (uu___24, false)
                                        | (FStar_Pervasives_Native.Some
                                           (false), uu___21)::(uu___22,
                                                               (arg, uu___23))::[]
                                            ->
                                            let uu___24 =
                                              let uu___25 =
                                                FStarC_Syntax_Util.mk_neg arg in
                                              maybe_auto_squash uu___25 in
                                            (uu___24, false)
                                        | (uu___21, (p, uu___22))::(uu___23,
                                                                    (q,
                                                                    uu___24))::[]
                                            ->
                                            let uu___25 =
                                              FStarC_Syntax_Util.term_eq p q in
                                            (if uu___25
                                             then
                                               ((w FStarC_Syntax_Util.t_true),
                                                 false)
                                             else
                                               squashed_head_un_auto_squash_args
                                                 tm1)
                                        | uu___21 ->
                                            squashed_head_un_auto_squash_args
                                              tm1
                                      else
                                        (let uu___21 =
                                           FStarC_Syntax_Syntax.fv_eq_lid fv
                                             FStarC_Parser_Const.not_lid in
                                         if uu___21
                                         then
                                           let uu___22 =
                                             FStarC_Compiler_List.map
                                               simplify args in
                                           match uu___22 with
                                           | (FStar_Pervasives_Native.Some
                                              (true), uu___23)::[] ->
                                               ((w FStarC_Syntax_Util.t_false),
                                                 false)
                                           | (FStar_Pervasives_Native.Some
                                              (false), uu___23)::[] ->
                                               ((w FStarC_Syntax_Util.t_true),
                                                 false)
                                           | uu___23 ->
                                               squashed_head_un_auto_squash_args
                                                 tm1
                                         else
                                           (let uu___23 =
                                              FStarC_Syntax_Syntax.fv_eq_lid
                                                fv
                                                FStarC_Parser_Const.forall_lid in
                                            if uu___23
                                            then
                                              match args with
                                              | (t, uu___24)::[] ->
                                                  let uu___25 =
                                                    let uu___26 =
                                                      FStarC_Syntax_Subst.compress
                                                        t in
                                                    uu___26.FStarC_Syntax_Syntax.n in
                                                  (match uu___25 with
                                                   | FStarC_Syntax_Syntax.Tm_abs
                                                       {
                                                         FStarC_Syntax_Syntax.bs
                                                           = uu___26::[];
                                                         FStarC_Syntax_Syntax.body
                                                           = body;
                                                         FStarC_Syntax_Syntax.rc_opt
                                                           = uu___27;_}
                                                       ->
                                                       let uu___28 =
                                                         simp_t body in
                                                       (match uu___28 with
                                                        | FStar_Pervasives_Native.Some
                                                            (true) ->
                                                            ((w
                                                                FStarC_Syntax_Util.t_true),
                                                              false)
                                                        | uu___29 ->
                                                            (tm1, false))
                                                   | uu___26 -> (tm1, false))
                                              | (ty,
                                                 FStar_Pervasives_Native.Some
                                                 {
                                                   FStarC_Syntax_Syntax.aqual_implicit
                                                     = true;
                                                   FStarC_Syntax_Syntax.aqual_attributes
                                                     = uu___24;_})::(t,
                                                                    uu___25)::[]
                                                  ->
                                                  let uu___26 =
                                                    let uu___27 =
                                                      FStarC_Syntax_Subst.compress
                                                        t in
                                                    uu___27.FStarC_Syntax_Syntax.n in
                                                  (match uu___26 with
                                                   | FStarC_Syntax_Syntax.Tm_abs
                                                       {
                                                         FStarC_Syntax_Syntax.bs
                                                           = uu___27::[];
                                                         FStarC_Syntax_Syntax.body
                                                           = body;
                                                         FStarC_Syntax_Syntax.rc_opt
                                                           = uu___28;_}
                                                       ->
                                                       let uu___29 =
                                                         simp_t body in
                                                       (match uu___29 with
                                                        | FStar_Pervasives_Native.Some
                                                            (true) ->
                                                            ((w
                                                                FStarC_Syntax_Util.t_true),
                                                              false)
                                                        | FStar_Pervasives_Native.Some
                                                            (false) when
                                                            clearly_inhabited
                                                              ty
                                                            ->
                                                            ((w
                                                                FStarC_Syntax_Util.t_false),
                                                              false)
                                                        | uu___30 ->
                                                            (tm1, false))
                                                   | uu___27 -> (tm1, false))
                                              | uu___24 -> (tm1, false)
                                            else
                                              (let uu___25 =
                                                 FStarC_Syntax_Syntax.fv_eq_lid
                                                   fv
                                                   FStarC_Parser_Const.exists_lid in
                                               if uu___25
                                               then
                                                 match args with
                                                 | (t, uu___26)::[] ->
                                                     let uu___27 =
                                                       let uu___28 =
                                                         FStarC_Syntax_Subst.compress
                                                           t in
                                                       uu___28.FStarC_Syntax_Syntax.n in
                                                     (match uu___27 with
                                                      | FStarC_Syntax_Syntax.Tm_abs
                                                          {
                                                            FStarC_Syntax_Syntax.bs
                                                              = uu___28::[];
                                                            FStarC_Syntax_Syntax.body
                                                              = body;
                                                            FStarC_Syntax_Syntax.rc_opt
                                                              = uu___29;_}
                                                          ->
                                                          let uu___30 =
                                                            simp_t body in
                                                          (match uu___30 with
                                                           | FStar_Pervasives_Native.Some
                                                               (false) ->
                                                               ((w
                                                                   FStarC_Syntax_Util.t_false),
                                                                 false)
                                                           | uu___31 ->
                                                               (tm1, false))
                                                      | uu___28 ->
                                                          (tm1, false))
                                                 | (ty,
                                                    FStar_Pervasives_Native.Some
                                                    {
                                                      FStarC_Syntax_Syntax.aqual_implicit
                                                        = true;
                                                      FStarC_Syntax_Syntax.aqual_attributes
                                                        = uu___26;_})::
                                                     (t, uu___27)::[] ->
                                                     let uu___28 =
                                                       let uu___29 =
                                                         FStarC_Syntax_Subst.compress
                                                           t in
                                                       uu___29.FStarC_Syntax_Syntax.n in
                                                     (match uu___28 with
                                                      | FStarC_Syntax_Syntax.Tm_abs
                                                          {
                                                            FStarC_Syntax_Syntax.bs
                                                              = uu___29::[];
                                                            FStarC_Syntax_Syntax.body
                                                              = body;
                                                            FStarC_Syntax_Syntax.rc_opt
                                                              = uu___30;_}
                                                          ->
                                                          let uu___31 =
                                                            simp_t body in
                                                          (match uu___31 with
                                                           | FStar_Pervasives_Native.Some
                                                               (false) ->
                                                               ((w
                                                                   FStarC_Syntax_Util.t_false),
                                                                 false)
                                                           | FStar_Pervasives_Native.Some
                                                               (true) when
                                                               clearly_inhabited
                                                                 ty
                                                               ->
                                                               ((w
                                                                   FStarC_Syntax_Util.t_true),
                                                                 false)
                                                           | uu___32 ->
                                                               (tm1, false))
                                                      | uu___29 ->
                                                          (tm1, false))
                                                 | uu___26 -> (tm1, false)
                                               else
                                                 (let uu___27 =
                                                    FStarC_Syntax_Syntax.fv_eq_lid
                                                      fv
                                                      FStarC_Parser_Const.b2t_lid in
                                                  if uu___27
                                                  then
                                                    match args with
                                                    | ({
                                                         FStarC_Syntax_Syntax.n
                                                           =
                                                           FStarC_Syntax_Syntax.Tm_constant
                                                           (FStarC_Const.Const_bool
                                                           (true));
                                                         FStarC_Syntax_Syntax.pos
                                                           = uu___28;
                                                         FStarC_Syntax_Syntax.vars
                                                           = uu___29;
                                                         FStarC_Syntax_Syntax.hash_code
                                                           = uu___30;_},
                                                       uu___31)::[] ->
                                                        ((w
                                                            FStarC_Syntax_Util.t_true),
                                                          false)
                                                    | ({
                                                         FStarC_Syntax_Syntax.n
                                                           =
                                                           FStarC_Syntax_Syntax.Tm_constant
                                                           (FStarC_Const.Const_bool
                                                           (false));
                                                         FStarC_Syntax_Syntax.pos
                                                           = uu___28;
                                                         FStarC_Syntax_Syntax.vars
                                                           = uu___29;
                                                         FStarC_Syntax_Syntax.hash_code
                                                           = uu___30;_},
                                                       uu___31)::[] ->
                                                        ((w
                                                            FStarC_Syntax_Util.t_false),
                                                          false)
                                                    | uu___28 -> (tm1, false)
                                                  else
                                                    (let uu___29 =
                                                       FStarC_Syntax_Syntax.fv_eq_lid
                                                         fv
                                                         FStarC_Parser_Const.haseq_lid in
                                                     if uu___29
                                                     then
                                                       let t_has_eq_for_sure
                                                         t =
                                                         let haseq_lids =
                                                           [FStarC_Parser_Const.int_lid;
                                                           FStarC_Parser_Const.bool_lid;
                                                           FStarC_Parser_Const.unit_lid;
                                                           FStarC_Parser_Const.string_lid] in
                                                         let uu___30 =
                                                           let uu___31 =
                                                             FStarC_Syntax_Subst.compress
                                                               t in
                                                           uu___31.FStarC_Syntax_Syntax.n in
                                                         match uu___30 with
                                                         | FStarC_Syntax_Syntax.Tm_fvar
                                                             fv1 when
                                                             FStarC_Compiler_List.existsb
                                                               (fun l ->
                                                                  FStarC_Syntax_Syntax.fv_eq_lid
                                                                    fv1 l)
                                                               haseq_lids
                                                             -> true
                                                         | uu___31 -> false in
                                                       (if
                                                          (FStarC_Compiler_List.length
                                                             args)
                                                            = Prims.int_one
                                                        then
                                                          let t =
                                                            let uu___30 =
                                                              FStarC_Compiler_List.hd
                                                                args in
                                                            FStar_Pervasives_Native.fst
                                                              uu___30 in
                                                          let uu___30 =
                                                            t_has_eq_for_sure
                                                              t in
                                                          (if uu___30
                                                           then
                                                             ((w
                                                                 FStarC_Syntax_Util.t_true),
                                                               false)
                                                           else
                                                             (let uu___32 =
                                                                let uu___33 =
                                                                  FStarC_Syntax_Subst.compress
                                                                    t in
                                                                uu___33.FStarC_Syntax_Syntax.n in
                                                              match uu___32
                                                              with
                                                              | FStarC_Syntax_Syntax.Tm_refine
                                                                  uu___33 ->
                                                                  let t1 =
                                                                    FStarC_Syntax_Util.unrefine
                                                                    t in
                                                                  let uu___34
                                                                    =
                                                                    t_has_eq_for_sure
                                                                    t1 in
                                                                  if uu___34
                                                                  then
                                                                    ((w
                                                                    FStarC_Syntax_Util.t_true),
                                                                    false)
                                                                  else
                                                                    (
                                                                    let haseq_tm
                                                                    =
                                                                    let uu___36
                                                                    =
                                                                    let uu___37
                                                                    =
                                                                    FStarC_Syntax_Subst.compress
                                                                    tm1 in
                                                                    uu___37.FStarC_Syntax_Syntax.n in
                                                                    match uu___36
                                                                    with
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Tm_app
                                                                    {
                                                                    FStarC_Syntax_Syntax.hd
                                                                    = hd;
                                                                    FStarC_Syntax_Syntax.args
                                                                    = uu___37;_}
                                                                    -> hd
                                                                    | 
                                                                    uu___37
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app" in
                                                                    let uu___36
                                                                    =
                                                                    let uu___37
                                                                    =
                                                                    let uu___38
                                                                    =
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    t1 in
                                                                    [uu___38] in
                                                                    FStarC_Syntax_Util.mk_app
                                                                    haseq_tm
                                                                    uu___37 in
                                                                    (uu___36,
                                                                    false))
                                                              | uu___33 ->
                                                                  (tm1,
                                                                    false)))
                                                        else (tm1, false))
                                                     else
                                                       (let uu___31 =
                                                          FStarC_Syntax_Syntax.fv_eq_lid
                                                            fv
                                                            FStarC_Parser_Const.subtype_of_lid in
                                                        if uu___31
                                                        then
                                                          let is_unit ty =
                                                            let uu___32 =
                                                              let uu___33 =
                                                                FStarC_Syntax_Subst.compress
                                                                  ty in
                                                              uu___33.FStarC_Syntax_Syntax.n in
                                                            match uu___32
                                                            with
                                                            | FStarC_Syntax_Syntax.Tm_fvar
                                                                fv1 ->
                                                                FStarC_Syntax_Syntax.fv_eq_lid
                                                                  fv1
                                                                  FStarC_Parser_Const.unit_lid
                                                            | uu___33 ->
                                                                false in
                                                          match args with
                                                          | (t, uu___32)::
                                                              (ty, uu___33)::[]
                                                              when
                                                              (is_unit ty) &&
                                                                (FStarC_Syntax_Util.is_sub_singleton
                                                                   t)
                                                              ->
                                                              ((w
                                                                  FStarC_Syntax_Util.t_true),
                                                                false)
                                                          | uu___32 ->
                                                              (tm1, false)
                                                        else
                                                          (let uu___33 =
                                                             FStarC_Syntax_Util.is_auto_squash
                                                               tm1 in
                                                           match uu___33 with
                                                           | FStar_Pervasives_Native.Some
                                                               (FStarC_Syntax_Syntax.U_zero,
                                                                t)
                                                               when
                                                               FStarC_Syntax_Util.is_sub_singleton
                                                                 t
                                                               -> (t, false)
                                                           | uu___34 ->
                                                               let uu___35 =
                                                                 let uu___36
                                                                   =
                                                                   norm_cb
                                                                    cfg in
                                                                 reduce_equality
                                                                   uu___36
                                                                   cfg env1 in
                                                               uu___35 tm1)))))))))))
                      | FStarC_Syntax_Syntax.Tm_app
                          {
                            FStarC_Syntax_Syntax.hd =
                              {
                                FStarC_Syntax_Syntax.n =
                                  FStarC_Syntax_Syntax.Tm_fvar fv;
                                FStarC_Syntax_Syntax.pos = uu___4;
                                FStarC_Syntax_Syntax.vars = uu___5;
                                FStarC_Syntax_Syntax.hash_code = uu___6;_};
                            FStarC_Syntax_Syntax.args = args;_}
                          ->
                          let uu___7 =
                            FStarC_Syntax_Syntax.fv_eq_lid fv
                              FStarC_Parser_Const.squash_lid in
                          if uu___7
                          then squashed_head_un_auto_squash_args tm1
                          else
                            (let uu___9 =
                               FStarC_Syntax_Syntax.fv_eq_lid fv
                                 FStarC_Parser_Const.and_lid in
                             if uu___9
                             then
                               let uu___10 =
                                 FStarC_Compiler_List.map simplify args in
                               match uu___10 with
                               | (FStar_Pervasives_Native.Some (true),
                                  uu___11)::(uu___12, (arg, uu___13))::[] ->
                                   let uu___14 = maybe_auto_squash arg in
                                   (uu___14, false)
                               | (uu___11, (arg, uu___12))::(FStar_Pervasives_Native.Some
                                                             (true), uu___13)::[]
                                   ->
                                   let uu___14 = maybe_auto_squash arg in
                                   (uu___14, false)
                               | (FStar_Pervasives_Native.Some (false),
                                  uu___11)::uu___12::[] ->
                                   ((w FStarC_Syntax_Util.t_false), false)
                               | uu___11::(FStar_Pervasives_Native.Some
                                           (false), uu___12)::[]
                                   -> ((w FStarC_Syntax_Util.t_false), false)
                               | uu___11 ->
                                   squashed_head_un_auto_squash_args tm1
                             else
                               (let uu___11 =
                                  FStarC_Syntax_Syntax.fv_eq_lid fv
                                    FStarC_Parser_Const.or_lid in
                                if uu___11
                                then
                                  let uu___12 =
                                    FStarC_Compiler_List.map simplify args in
                                  match uu___12 with
                                  | (FStar_Pervasives_Native.Some (true),
                                     uu___13)::uu___14::[] ->
                                      ((w FStarC_Syntax_Util.t_true), false)
                                  | uu___13::(FStar_Pervasives_Native.Some
                                              (true), uu___14)::[]
                                      ->
                                      ((w FStarC_Syntax_Util.t_true), false)
                                  | (FStar_Pervasives_Native.Some (false),
                                     uu___13)::(uu___14, (arg, uu___15))::[]
                                      ->
                                      let uu___16 = maybe_auto_squash arg in
                                      (uu___16, false)
                                  | (uu___13, (arg, uu___14))::(FStar_Pervasives_Native.Some
                                                                (false),
                                                                uu___15)::[]
                                      ->
                                      let uu___16 = maybe_auto_squash arg in
                                      (uu___16, false)
                                  | uu___13 ->
                                      squashed_head_un_auto_squash_args tm1
                                else
                                  (let uu___13 =
                                     FStarC_Syntax_Syntax.fv_eq_lid fv
                                       FStarC_Parser_Const.imp_lid in
                                   if uu___13
                                   then
                                     let uu___14 =
                                       FStarC_Compiler_List.map simplify args in
                                     match uu___14 with
                                     | uu___15::(FStar_Pervasives_Native.Some
                                                 (true), uu___16)::[]
                                         ->
                                         ((w FStarC_Syntax_Util.t_true),
                                           false)
                                     | (FStar_Pervasives_Native.Some (false),
                                        uu___15)::uu___16::[] ->
                                         ((w FStarC_Syntax_Util.t_true),
                                           false)
                                     | (FStar_Pervasives_Native.Some (true),
                                        uu___15)::(uu___16, (arg, uu___17))::[]
                                         ->
                                         let uu___18 = maybe_auto_squash arg in
                                         (uu___18, false)
                                     | (uu___15, (p, uu___16))::(uu___17,
                                                                 (q, uu___18))::[]
                                         ->
                                         let uu___19 =
                                           FStarC_Syntax_Util.term_eq p q in
                                         (if uu___19
                                          then
                                            ((w FStarC_Syntax_Util.t_true),
                                              false)
                                          else
                                            squashed_head_un_auto_squash_args
                                              tm1)
                                     | uu___15 ->
                                         squashed_head_un_auto_squash_args
                                           tm1
                                   else
                                     (let uu___15 =
                                        FStarC_Syntax_Syntax.fv_eq_lid fv
                                          FStarC_Parser_Const.iff_lid in
                                      if uu___15
                                      then
                                        let uu___16 =
                                          FStarC_Compiler_List.map simplify
                                            args in
                                        match uu___16 with
                                        | (FStar_Pervasives_Native.Some
                                           (true), uu___17)::(FStar_Pervasives_Native.Some
                                                              (true),
                                                              uu___18)::[]
                                            ->
                                            ((w FStarC_Syntax_Util.t_true),
                                              false)
                                        | (FStar_Pervasives_Native.Some
                                           (false), uu___17)::(FStar_Pervasives_Native.Some
                                                               (false),
                                                               uu___18)::[]
                                            ->
                                            ((w FStarC_Syntax_Util.t_true),
                                              false)
                                        | (FStar_Pervasives_Native.Some
                                           (true), uu___17)::(FStar_Pervasives_Native.Some
                                                              (false),
                                                              uu___18)::[]
                                            ->
                                            ((w FStarC_Syntax_Util.t_false),
                                              false)
                                        | (FStar_Pervasives_Native.Some
                                           (false), uu___17)::(FStar_Pervasives_Native.Some
                                                               (true),
                                                               uu___18)::[]
                                            ->
                                            ((w FStarC_Syntax_Util.t_false),
                                              false)
                                        | (uu___17, (arg, uu___18))::
                                            (FStar_Pervasives_Native.Some
                                             (true), uu___19)::[]
                                            ->
                                            let uu___20 =
                                              maybe_auto_squash arg in
                                            (uu___20, false)
                                        | (FStar_Pervasives_Native.Some
                                           (true), uu___17)::(uu___18,
                                                              (arg, uu___19))::[]
                                            ->
                                            let uu___20 =
                                              maybe_auto_squash arg in
                                            (uu___20, false)
                                        | (uu___17, (arg, uu___18))::
                                            (FStar_Pervasives_Native.Some
                                             (false), uu___19)::[]
                                            ->
                                            let uu___20 =
                                              let uu___21 =
                                                FStarC_Syntax_Util.mk_neg arg in
                                              maybe_auto_squash uu___21 in
                                            (uu___20, false)
                                        | (FStar_Pervasives_Native.Some
                                           (false), uu___17)::(uu___18,
                                                               (arg, uu___19))::[]
                                            ->
                                            let uu___20 =
                                              let uu___21 =
                                                FStarC_Syntax_Util.mk_neg arg in
                                              maybe_auto_squash uu___21 in
                                            (uu___20, false)
                                        | (uu___17, (p, uu___18))::(uu___19,
                                                                    (q,
                                                                    uu___20))::[]
                                            ->
                                            let uu___21 =
                                              FStarC_Syntax_Util.term_eq p q in
                                            (if uu___21
                                             then
                                               ((w FStarC_Syntax_Util.t_true),
                                                 false)
                                             else
                                               squashed_head_un_auto_squash_args
                                                 tm1)
                                        | uu___17 ->
                                            squashed_head_un_auto_squash_args
                                              tm1
                                      else
                                        (let uu___17 =
                                           FStarC_Syntax_Syntax.fv_eq_lid fv
                                             FStarC_Parser_Const.not_lid in
                                         if uu___17
                                         then
                                           let uu___18 =
                                             FStarC_Compiler_List.map
                                               simplify args in
                                           match uu___18 with
                                           | (FStar_Pervasives_Native.Some
                                              (true), uu___19)::[] ->
                                               ((w FStarC_Syntax_Util.t_false),
                                                 false)
                                           | (FStar_Pervasives_Native.Some
                                              (false), uu___19)::[] ->
                                               ((w FStarC_Syntax_Util.t_true),
                                                 false)
                                           | uu___19 ->
                                               squashed_head_un_auto_squash_args
                                                 tm1
                                         else
                                           (let uu___19 =
                                              FStarC_Syntax_Syntax.fv_eq_lid
                                                fv
                                                FStarC_Parser_Const.forall_lid in
                                            if uu___19
                                            then
                                              match args with
                                              | (t, uu___20)::[] ->
                                                  let uu___21 =
                                                    let uu___22 =
                                                      FStarC_Syntax_Subst.compress
                                                        t in
                                                    uu___22.FStarC_Syntax_Syntax.n in
                                                  (match uu___21 with
                                                   | FStarC_Syntax_Syntax.Tm_abs
                                                       {
                                                         FStarC_Syntax_Syntax.bs
                                                           = uu___22::[];
                                                         FStarC_Syntax_Syntax.body
                                                           = body;
                                                         FStarC_Syntax_Syntax.rc_opt
                                                           = uu___23;_}
                                                       ->
                                                       let uu___24 =
                                                         simp_t body in
                                                       (match uu___24 with
                                                        | FStar_Pervasives_Native.Some
                                                            (true) ->
                                                            ((w
                                                                FStarC_Syntax_Util.t_true),
                                                              false)
                                                        | uu___25 ->
                                                            (tm1, false))
                                                   | uu___22 -> (tm1, false))
                                              | (ty,
                                                 FStar_Pervasives_Native.Some
                                                 {
                                                   FStarC_Syntax_Syntax.aqual_implicit
                                                     = true;
                                                   FStarC_Syntax_Syntax.aqual_attributes
                                                     = uu___20;_})::(t,
                                                                    uu___21)::[]
                                                  ->
                                                  let uu___22 =
                                                    let uu___23 =
                                                      FStarC_Syntax_Subst.compress
                                                        t in
                                                    uu___23.FStarC_Syntax_Syntax.n in
                                                  (match uu___22 with
                                                   | FStarC_Syntax_Syntax.Tm_abs
                                                       {
                                                         FStarC_Syntax_Syntax.bs
                                                           = uu___23::[];
                                                         FStarC_Syntax_Syntax.body
                                                           = body;
                                                         FStarC_Syntax_Syntax.rc_opt
                                                           = uu___24;_}
                                                       ->
                                                       let uu___25 =
                                                         simp_t body in
                                                       (match uu___25 with
                                                        | FStar_Pervasives_Native.Some
                                                            (true) ->
                                                            ((w
                                                                FStarC_Syntax_Util.t_true),
                                                              false)
                                                        | FStar_Pervasives_Native.Some
                                                            (false) when
                                                            clearly_inhabited
                                                              ty
                                                            ->
                                                            ((w
                                                                FStarC_Syntax_Util.t_false),
                                                              false)
                                                        | uu___26 ->
                                                            (tm1, false))
                                                   | uu___23 -> (tm1, false))
                                              | uu___20 -> (tm1, false)
                                            else
                                              (let uu___21 =
                                                 FStarC_Syntax_Syntax.fv_eq_lid
                                                   fv
                                                   FStarC_Parser_Const.exists_lid in
                                               if uu___21
                                               then
                                                 match args with
                                                 | (t, uu___22)::[] ->
                                                     let uu___23 =
                                                       let uu___24 =
                                                         FStarC_Syntax_Subst.compress
                                                           t in
                                                       uu___24.FStarC_Syntax_Syntax.n in
                                                     (match uu___23 with
                                                      | FStarC_Syntax_Syntax.Tm_abs
                                                          {
                                                            FStarC_Syntax_Syntax.bs
                                                              = uu___24::[];
                                                            FStarC_Syntax_Syntax.body
                                                              = body;
                                                            FStarC_Syntax_Syntax.rc_opt
                                                              = uu___25;_}
                                                          ->
                                                          let uu___26 =
                                                            simp_t body in
                                                          (match uu___26 with
                                                           | FStar_Pervasives_Native.Some
                                                               (false) ->
                                                               ((w
                                                                   FStarC_Syntax_Util.t_false),
                                                                 false)
                                                           | uu___27 ->
                                                               (tm1, false))
                                                      | uu___24 ->
                                                          (tm1, false))
                                                 | (ty,
                                                    FStar_Pervasives_Native.Some
                                                    {
                                                      FStarC_Syntax_Syntax.aqual_implicit
                                                        = true;
                                                      FStarC_Syntax_Syntax.aqual_attributes
                                                        = uu___22;_})::
                                                     (t, uu___23)::[] ->
                                                     let uu___24 =
                                                       let uu___25 =
                                                         FStarC_Syntax_Subst.compress
                                                           t in
                                                       uu___25.FStarC_Syntax_Syntax.n in
                                                     (match uu___24 with
                                                      | FStarC_Syntax_Syntax.Tm_abs
                                                          {
                                                            FStarC_Syntax_Syntax.bs
                                                              = uu___25::[];
                                                            FStarC_Syntax_Syntax.body
                                                              = body;
                                                            FStarC_Syntax_Syntax.rc_opt
                                                              = uu___26;_}
                                                          ->
                                                          let uu___27 =
                                                            simp_t body in
                                                          (match uu___27 with
                                                           | FStar_Pervasives_Native.Some
                                                               (false) ->
                                                               ((w
                                                                   FStarC_Syntax_Util.t_false),
                                                                 false)
                                                           | FStar_Pervasives_Native.Some
                                                               (true) when
                                                               clearly_inhabited
                                                                 ty
                                                               ->
                                                               ((w
                                                                   FStarC_Syntax_Util.t_true),
                                                                 false)
                                                           | uu___28 ->
                                                               (tm1, false))
                                                      | uu___25 ->
                                                          (tm1, false))
                                                 | uu___22 -> (tm1, false)
                                               else
                                                 (let uu___23 =
                                                    FStarC_Syntax_Syntax.fv_eq_lid
                                                      fv
                                                      FStarC_Parser_Const.b2t_lid in
                                                  if uu___23
                                                  then
                                                    match args with
                                                    | ({
                                                         FStarC_Syntax_Syntax.n
                                                           =
                                                           FStarC_Syntax_Syntax.Tm_constant
                                                           (FStarC_Const.Const_bool
                                                           (true));
                                                         FStarC_Syntax_Syntax.pos
                                                           = uu___24;
                                                         FStarC_Syntax_Syntax.vars
                                                           = uu___25;
                                                         FStarC_Syntax_Syntax.hash_code
                                                           = uu___26;_},
                                                       uu___27)::[] ->
                                                        ((w
                                                            FStarC_Syntax_Util.t_true),
                                                          false)
                                                    | ({
                                                         FStarC_Syntax_Syntax.n
                                                           =
                                                           FStarC_Syntax_Syntax.Tm_constant
                                                           (FStarC_Const.Const_bool
                                                           (false));
                                                         FStarC_Syntax_Syntax.pos
                                                           = uu___24;
                                                         FStarC_Syntax_Syntax.vars
                                                           = uu___25;
                                                         FStarC_Syntax_Syntax.hash_code
                                                           = uu___26;_},
                                                       uu___27)::[] ->
                                                        ((w
                                                            FStarC_Syntax_Util.t_false),
                                                          false)
                                                    | uu___24 -> (tm1, false)
                                                  else
                                                    (let uu___25 =
                                                       FStarC_Syntax_Syntax.fv_eq_lid
                                                         fv
                                                         FStarC_Parser_Const.haseq_lid in
                                                     if uu___25
                                                     then
                                                       let t_has_eq_for_sure
                                                         t =
                                                         let haseq_lids =
                                                           [FStarC_Parser_Const.int_lid;
                                                           FStarC_Parser_Const.bool_lid;
                                                           FStarC_Parser_Const.unit_lid;
                                                           FStarC_Parser_Const.string_lid] in
                                                         let uu___26 =
                                                           let uu___27 =
                                                             FStarC_Syntax_Subst.compress
                                                               t in
                                                           uu___27.FStarC_Syntax_Syntax.n in
                                                         match uu___26 with
                                                         | FStarC_Syntax_Syntax.Tm_fvar
                                                             fv1 when
                                                             FStarC_Compiler_List.existsb
                                                               (fun l ->
                                                                  FStarC_Syntax_Syntax.fv_eq_lid
                                                                    fv1 l)
                                                               haseq_lids
                                                             -> true
                                                         | uu___27 -> false in
                                                       (if
                                                          (FStarC_Compiler_List.length
                                                             args)
                                                            = Prims.int_one
                                                        then
                                                          let t =
                                                            let uu___26 =
                                                              FStarC_Compiler_List.hd
                                                                args in
                                                            FStar_Pervasives_Native.fst
                                                              uu___26 in
                                                          let uu___26 =
                                                            t_has_eq_for_sure
                                                              t in
                                                          (if uu___26
                                                           then
                                                             ((w
                                                                 FStarC_Syntax_Util.t_true),
                                                               false)
                                                           else
                                                             (let uu___28 =
                                                                let uu___29 =
                                                                  FStarC_Syntax_Subst.compress
                                                                    t in
                                                                uu___29.FStarC_Syntax_Syntax.n in
                                                              match uu___28
                                                              with
                                                              | FStarC_Syntax_Syntax.Tm_refine
                                                                  uu___29 ->
                                                                  let t1 =
                                                                    FStarC_Syntax_Util.unrefine
                                                                    t in
                                                                  let uu___30
                                                                    =
                                                                    t_has_eq_for_sure
                                                                    t1 in
                                                                  if uu___30
                                                                  then
                                                                    ((w
                                                                    FStarC_Syntax_Util.t_true),
                                                                    false)
                                                                  else
                                                                    (
                                                                    let haseq_tm
                                                                    =
                                                                    let uu___32
                                                                    =
                                                                    let uu___33
                                                                    =
                                                                    FStarC_Syntax_Subst.compress
                                                                    tm1 in
                                                                    uu___33.FStarC_Syntax_Syntax.n in
                                                                    match uu___32
                                                                    with
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Tm_app
                                                                    {
                                                                    FStarC_Syntax_Syntax.hd
                                                                    = hd;
                                                                    FStarC_Syntax_Syntax.args
                                                                    = uu___33;_}
                                                                    -> hd
                                                                    | 
                                                                    uu___33
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app" in
                                                                    let uu___32
                                                                    =
                                                                    let uu___33
                                                                    =
                                                                    let uu___34
                                                                    =
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    t1 in
                                                                    [uu___34] in
                                                                    FStarC_Syntax_Util.mk_app
                                                                    haseq_tm
                                                                    uu___33 in
                                                                    (uu___32,
                                                                    false))
                                                              | uu___29 ->
                                                                  (tm1,
                                                                    false)))
                                                        else (tm1, false))
                                                     else
                                                       (let uu___27 =
                                                          FStarC_Syntax_Syntax.fv_eq_lid
                                                            fv
                                                            FStarC_Parser_Const.subtype_of_lid in
                                                        if uu___27
                                                        then
                                                          let is_unit ty =
                                                            let uu___28 =
                                                              let uu___29 =
                                                                FStarC_Syntax_Subst.compress
                                                                  ty in
                                                              uu___29.FStarC_Syntax_Syntax.n in
                                                            match uu___28
                                                            with
                                                            | FStarC_Syntax_Syntax.Tm_fvar
                                                                fv1 ->
                                                                FStarC_Syntax_Syntax.fv_eq_lid
                                                                  fv1
                                                                  FStarC_Parser_Const.unit_lid
                                                            | uu___29 ->
                                                                false in
                                                          match args with
                                                          | (t, uu___28)::
                                                              (ty, uu___29)::[]
                                                              when
                                                              (is_unit ty) &&
                                                                (FStarC_Syntax_Util.is_sub_singleton
                                                                   t)
                                                              ->
                                                              ((w
                                                                  FStarC_Syntax_Util.t_true),
                                                                false)
                                                          | uu___28 ->
                                                              (tm1, false)
                                                        else
                                                          (let uu___29 =
                                                             FStarC_Syntax_Util.is_auto_squash
                                                               tm1 in
                                                           match uu___29 with
                                                           | FStar_Pervasives_Native.Some
                                                               (FStarC_Syntax_Syntax.U_zero,
                                                                t)
                                                               when
                                                               FStarC_Syntax_Util.is_sub_singleton
                                                                 t
                                                               -> (t, false)
                                                           | uu___30 ->
                                                               let uu___31 =
                                                                 let uu___32
                                                                   =
                                                                   norm_cb
                                                                    cfg in
                                                                 reduce_equality
                                                                   uu___32
                                                                   cfg env1 in
                                                               uu___31 tm1)))))))))))
                      | FStarC_Syntax_Syntax.Tm_refine
                          { FStarC_Syntax_Syntax.b = bv;
                            FStarC_Syntax_Syntax.phi = t;_}
                          ->
                          let uu___4 = simp_t t in
                          (match uu___4 with
                           | FStar_Pervasives_Native.Some (true) ->
                               ((bv.FStarC_Syntax_Syntax.sort), false)
                           | FStar_Pervasives_Native.Some (false) ->
                               (tm1, false)
                           | FStar_Pervasives_Native.None -> (tm1, false))
                      | FStarC_Syntax_Syntax.Tm_match uu___4 ->
                          let uu___5 = is_const_match tm1 in
                          (match uu___5 with
                           | FStar_Pervasives_Native.Some (true) ->
                               ((w FStarC_Syntax_Util.t_true), false)
                           | FStar_Pervasives_Native.Some (false) ->
                               ((w FStarC_Syntax_Util.t_false), false)
                           | FStar_Pervasives_Native.None -> (tm1, false))
                      | uu___4 -> (tm1, false)))
and (rebuild :
  FStarC_TypeChecker_Cfg.cfg ->
    env -> stack -> FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun t ->
          FStarC_TypeChecker_Cfg.log cfg
            (fun uu___1 ->
               (let uu___3 =
                  FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term
                    t in
                let uu___4 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
                let uu___5 =
                  FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                    (FStarC_Compiler_List.length env1) in
                let uu___6 =
                  let uu___7 =
                    let uu___8 = firstn (Prims.of_int (4)) stack1 in
                    FStar_Pervasives_Native.fst uu___8 in
                  FStarC_Class_Show.show
                    (FStarC_Class_Show.show_list showable_stack_elt) uu___7 in
                FStarC_Compiler_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s\n"
                  uu___3 uu___4 uu___5 uu___6);
               (let uu___3 = FStarC_Compiler_Effect.op_Bang dbg_NormRebuild in
                if uu___3
                then
                  let uu___4 = FStarC_Syntax_Util.unbound_variables t in
                  match uu___4 with
                  | [] -> ()
                  | bvs ->
                      ((let uu___6 =
                          FStarC_Class_Tagged.tag_of
                            FStarC_Syntax_Syntax.tagged_term t in
                        let uu___7 =
                          FStarC_Class_Show.show
                            FStarC_Syntax_Print.showable_term t in
                        let uu___8 =
                          FStarC_Class_Show.show
                            (FStarC_Class_Show.show_list
                               FStarC_Syntax_Print.showable_bv) bvs in
                        FStarC_Compiler_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu___6 uu___7
                          uu___8);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t in
           if
             (FStarC_Compiler_Util.is_some f_opt) &&
               (match stack1 with
                | (Arg uu___1)::uu___2 -> true
                | uu___1 -> false)
           then
             let uu___1 = FStarC_Compiler_Util.must f_opt in
             norm cfg env1 stack1 uu___1
           else
             (let uu___2 = maybe_simplify cfg env1 stack1 t in
              match uu___2 with
              | (t1, renorm) ->
                  if renorm
                  then norm cfg env1 stack1 t1
                  else do_rebuild cfg env1 stack1 t1))
and (do_rebuild :
  FStarC_TypeChecker_Cfg.cfg ->
    env -> stack -> FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun cfg ->
    fun env1 ->
      fun stack1 ->
        fun t ->
          match stack1 with
          | [] -> t
          | (Meta (uu___, m, r))::stack2 ->
              let t1 =
                match m with
                | FStarC_Syntax_Syntax.Meta_monadic uu___1 ->
                    let uu___2 =
                      let uu___3 = FStarC_Syntax_Subst.compress t in
                      uu___3.FStarC_Syntax_Syntax.n in
                    (match uu___2 with
                     | FStarC_Syntax_Syntax.Tm_meta
                         { FStarC_Syntax_Syntax.tm2 = t';
                           FStarC_Syntax_Syntax.meta =
                             FStarC_Syntax_Syntax.Meta_monadic uu___3;_}
                         ->
                         FStarC_Syntax_Syntax.mk
                           (FStarC_Syntax_Syntax.Tm_meta
                              {
                                FStarC_Syntax_Syntax.tm2 = t';
                                FStarC_Syntax_Syntax.meta = m
                              }) r
                     | uu___3 ->
                         FStarC_Syntax_Syntax.mk
                           (FStarC_Syntax_Syntax.Tm_meta
                              {
                                FStarC_Syntax_Syntax.tm2 = t;
                                FStarC_Syntax_Syntax.meta = m
                              }) r)
                | uu___1 ->
                    FStarC_Syntax_Syntax.mk
                      (FStarC_Syntax_Syntax.Tm_meta
                         {
                           FStarC_Syntax_Syntax.tm2 = t;
                           FStarC_Syntax_Syntax.meta = m
                         }) r in
              rebuild cfg env1 stack2 t1
          | (MemoLazy r)::stack2 ->
              (set_memo cfg r (env1, t);
               FStarC_TypeChecker_Cfg.log cfg
                 (fun uu___2 ->
                    let uu___3 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_term t in
                    FStarC_Compiler_Util.print1 "\tSet memo %s\n" uu___3);
               rebuild cfg env1 stack2 t)
          | (Let (env', bs, lb, r))::stack2 ->
              let body = FStarC_Syntax_Subst.close bs t in
              let t1 =
                FStarC_Syntax_Syntax.mk
                  (FStarC_Syntax_Syntax.Tm_let
                     {
                       FStarC_Syntax_Syntax.lbs = (false, [lb]);
                       FStarC_Syntax_Syntax.body1 = body
                     }) r in
              rebuild cfg env' stack2 t1
          | (Abs (env', bs, env'', lopt, r))::stack2 ->
              let bs1 = norm_binders cfg env' bs in
              let lopt1 =
                FStarC_Compiler_Util.map_option
                  (norm_residual_comp cfg env'') lopt in
              let uu___ =
                let uu___1 = FStarC_Syntax_Util.abs bs1 t lopt1 in
                {
                  FStarC_Syntax_Syntax.n = (uu___1.FStarC_Syntax_Syntax.n);
                  FStarC_Syntax_Syntax.pos = r;
                  FStarC_Syntax_Syntax.vars =
                    (uu___1.FStarC_Syntax_Syntax.vars);
                  FStarC_Syntax_Syntax.hash_code =
                    (uu___1.FStarC_Syntax_Syntax.hash_code)
                } in
              rebuild cfg env1 stack2 uu___
          | (Arg (Univ uu___, uu___1, uu___2))::uu___3 ->
              failwith "Impossible"
          | (Arg (Dummy, uu___, uu___1))::uu___2 -> failwith "Impossible"
          | (UnivArgs (us, r))::stack2 ->
              let t1 = FStarC_Syntax_Syntax.mk_Tm_uinst t us in
              rebuild cfg env1 stack2 t1
          | (Arg (Clos (env_arg, tm, uu___, uu___1), aq, r))::stack2 when
              let uu___2 = head_of t in
              FStarC_Syntax_Util.is_fstar_tactics_by_tactic uu___2 ->
              let t1 =
                let uu___2 =
                  let uu___3 = closure_as_term cfg env_arg tm in (uu___3, aq) in
                FStarC_Syntax_Syntax.extend_app t uu___2 r in
              rebuild cfg env1 stack2 t1
          | (Arg (Clos (env_arg, tm, m, uu___), aq, r))::stack2 ->
              (FStarC_TypeChecker_Cfg.log cfg
                 (fun uu___2 ->
                    let uu___3 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_term tm in
                    FStarC_Compiler_Util.print1 "Rebuilding with arg %s\n"
                      uu___3);
               (let uu___2 =
                  (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.hnf
                    &&
                    (let uu___3 = is_partial_primop_app cfg t in
                     Prims.op_Negation uu___3) in
                if uu___2
                then
                  let arg = closure_as_term cfg env_arg tm in
                  let t1 = FStarC_Syntax_Syntax.extend_app t (arg, aq) r in
                  rebuild cfg env_arg stack2 t1
                else
                  (let uu___4 = read_memo cfg m in
                   match uu___4 with
                   | FStar_Pervasives_Native.Some (uu___5, a) ->
                       let t1 = FStarC_Syntax_Syntax.extend_app t (a, aq) r in
                       rebuild cfg env_arg stack2 t1
                   | FStar_Pervasives_Native.None when
                       Prims.op_Negation
                         (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.iota
                       ->
                       let stack3 = (App (env1, t, aq, r)) :: stack2 in
                       norm cfg env_arg stack3 tm
                   | FStar_Pervasives_Native.None ->
                       let stack3 = (MemoLazy m) :: (App (env1, t, aq, r)) ::
                         stack2 in
                       norm cfg env_arg stack3 tm)))
          | (App (env2, head, aq, r))::stack' when should_reify cfg stack1 ->
              let t0 = t in
              let fallback msg uu___ =
                FStarC_TypeChecker_Cfg.log cfg
                  (fun uu___2 ->
                     let uu___3 =
                       FStarC_Class_Show.show
                         FStarC_Syntax_Print.showable_term t in
                     FStarC_Compiler_Util.print2 "Not reifying%s: %s\n" msg
                       uu___3);
                (let t1 = FStarC_Syntax_Syntax.extend_app head (t, aq) r in
                 rebuild cfg env2 stack' t1) in
              let is_non_tac_layered_effect m =
                let norm_m =
                  FStarC_TypeChecker_Env.norm_eff_name
                    cfg.FStarC_TypeChecker_Cfg.tcenv m in
                (let uu___ =
                   FStarC_Ident.lid_equals norm_m
                     FStarC_Parser_Const.effect_TAC_lid in
                 Prims.op_Negation uu___) &&
                  (FStarC_TypeChecker_Env.is_layered_effect
                     cfg.FStarC_TypeChecker_Cfg.tcenv norm_m) in
              let uu___ =
                let uu___1 = FStarC_Syntax_Subst.compress t in
                uu___1.FStarC_Syntax_Syntax.n in
              (match uu___ with
               | FStarC_Syntax_Syntax.Tm_meta
                   { FStarC_Syntax_Syntax.tm2 = uu___1;
                     FStarC_Syntax_Syntax.meta =
                       FStarC_Syntax_Syntax.Meta_monadic (m, uu___2);_}
                   when
                   (is_non_tac_layered_effect m) &&
                     (Prims.op_Negation
                        (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction)
                   ->
                   let uu___3 =
                     let uu___4 = FStarC_Ident.string_of_lid m in
                     FStarC_Compiler_Util.format1
                       "Meta_monadic for a non-TAC layered effect %s in non-extraction mode"
                       uu___4 in
                   fallback uu___3 ()
               | FStarC_Syntax_Syntax.Tm_meta
                   { FStarC_Syntax_Syntax.tm2 = uu___1;
                     FStarC_Syntax_Syntax.meta =
                       FStarC_Syntax_Syntax.Meta_monadic (m, uu___2);_}
                   when
                   ((is_non_tac_layered_effect m) &&
                      (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction)
                     &&
                     (let uu___3 =
                        get_extraction_mode cfg.FStarC_TypeChecker_Cfg.tcenv
                          m in
                      FStarC_Syntax_Syntax.uu___is_Extract_none uu___3)
                   ->
                   let uu___3 =
                     get_extraction_mode cfg.FStarC_TypeChecker_Cfg.tcenv m in
                   (match uu___3 with
                    | FStarC_Syntax_Syntax.Extract_none msg ->
                        let uu___4 =
                          let uu___5 = FStarC_Ident.string_of_lid m in
                          FStarC_Compiler_Util.format2
                            "Normalizer cannot reify effect %s for extraction since %s"
                            uu___5 msg in
                        FStarC_Errors.raise_error
                          (FStarC_Syntax_Syntax.has_range_syntax ()) t
                          FStarC_Errors_Codes.Fatal_UnexpectedEffect ()
                          (Obj.magic
                             FStarC_Errors_Msg.is_error_message_string)
                          (Obj.magic uu___4))
               | FStarC_Syntax_Syntax.Tm_meta
                   { FStarC_Syntax_Syntax.tm2 = uu___1;
                     FStarC_Syntax_Syntax.meta =
                       FStarC_Syntax_Syntax.Meta_monadic (m, uu___2);_}
                   when
                   ((is_non_tac_layered_effect m) &&
                      (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction)
                     &&
                     (let uu___3 =
                        get_extraction_mode cfg.FStarC_TypeChecker_Cfg.tcenv
                          m in
                      uu___3 = FStarC_Syntax_Syntax.Extract_primitive)
                   ->
                   let uu___3 =
                     let uu___4 = FStarC_Ident.string_of_lid m in
                     FStarC_Compiler_Util.format1
                       "Meta_monadic for a non-TAC layered effect %s which is Extract_primtiive"
                       uu___4 in
                   fallback uu___3 ()
               | FStarC_Syntax_Syntax.Tm_meta
                   { FStarC_Syntax_Syntax.tm2 = uu___1;
                     FStarC_Syntax_Syntax.meta =
                       FStarC_Syntax_Syntax.Meta_monadic_lift
                       (msrc, mtgt, uu___2);_}
                   when
                   ((is_non_tac_layered_effect msrc) ||
                      (is_non_tac_layered_effect mtgt))
                     &&
                     (Prims.op_Negation
                        (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction)
                   ->
                   let uu___3 =
                     let uu___4 = FStarC_Ident.string_of_lid msrc in
                     let uu___5 = FStarC_Ident.string_of_lid mtgt in
                     FStarC_Compiler_Util.format2
                       "Meta_monadic_lift for a non-TAC layered effect %s ~> %s in non extraction mode"
                       uu___4 uu___5 in
                   fallback uu___3 ()
               | FStarC_Syntax_Syntax.Tm_meta
                   { FStarC_Syntax_Syntax.tm2 = uu___1;
                     FStarC_Syntax_Syntax.meta =
                       FStarC_Syntax_Syntax.Meta_monadic_lift
                       (msrc, mtgt, uu___2);_}
                   when
                   (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.for_extraction
                     &&
                     (((is_non_tac_layered_effect msrc) &&
                         (let uu___3 =
                            get_extraction_mode
                              cfg.FStarC_TypeChecker_Cfg.tcenv msrc in
                          FStarC_Syntax_Syntax.uu___is_Extract_none uu___3))
                        ||
                        ((is_non_tac_layered_effect mtgt) &&
                           (let uu___3 =
                              get_extraction_mode
                                cfg.FStarC_TypeChecker_Cfg.tcenv mtgt in
                            FStarC_Syntax_Syntax.uu___is_Extract_none uu___3)))
                   ->
                   let uu___3 =
                     let uu___4 = FStarC_Ident.string_of_lid msrc in
                     let uu___5 = FStarC_Ident.string_of_lid mtgt in
                     FStarC_Compiler_Util.format2
                       "Normalizer cannot reify %s ~> %s for extraction"
                       uu___4 uu___5 in
                   FStarC_Errors.raise_error
                     (FStarC_Syntax_Syntax.has_range_syntax ()) t
                     FStarC_Errors_Codes.Fatal_UnexpectedEffect ()
                     (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                     (Obj.magic uu___3)
               | FStarC_Syntax_Syntax.Tm_meta
                   { FStarC_Syntax_Syntax.tm2 = t1;
                     FStarC_Syntax_Syntax.meta =
                       FStarC_Syntax_Syntax.Meta_monadic (m, ty);_}
                   ->
                   do_reify_monadic (fallback " (1)") cfg env2 stack1 t1 m ty
               | FStarC_Syntax_Syntax.Tm_meta
                   { FStarC_Syntax_Syntax.tm2 = t1;
                     FStarC_Syntax_Syntax.meta =
                       FStarC_Syntax_Syntax.Meta_monadic_lift
                       (msrc, mtgt, ty);_}
                   ->
                   let lifted =
                     let uu___1 = closure_as_term cfg env2 ty in
                     reify_lift cfg t1 msrc mtgt uu___1 in
                   (FStarC_TypeChecker_Cfg.log cfg
                      (fun uu___2 ->
                         let uu___3 =
                           FStarC_Class_Show.show
                             FStarC_Syntax_Print.showable_term lifted in
                         FStarC_Compiler_Util.print1
                           "Reified lift to (1): %s\n" uu___3);
                    (let uu___2 = FStarC_Compiler_List.tl stack1 in
                     norm cfg env2 uu___2 lifted))
               | FStarC_Syntax_Syntax.Tm_app
                   {
                     FStarC_Syntax_Syntax.hd =
                       {
                         FStarC_Syntax_Syntax.n =
                           FStarC_Syntax_Syntax.Tm_constant
                           (FStarC_Const.Const_reflect uu___1);
                         FStarC_Syntax_Syntax.pos = uu___2;
                         FStarC_Syntax_Syntax.vars = uu___3;
                         FStarC_Syntax_Syntax.hash_code = uu___4;_};
                     FStarC_Syntax_Syntax.args = (e, uu___5)::[];_}
                   -> norm cfg env2 stack' e
               | FStarC_Syntax_Syntax.Tm_app uu___1 when
                   (cfg.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.primops
                   ->
                   let uu___2 =
                     FStarC_Syntax_Util.head_and_args_full_unmeta t in
                   (match uu___2 with
                    | (hd, args) ->
                        let uu___3 =
                          let uu___4 = FStarC_Syntax_Util.un_uinst hd in
                          uu___4.FStarC_Syntax_Syntax.n in
                        (match uu___3 with
                         | FStarC_Syntax_Syntax.Tm_fvar fv ->
                             let uu___4 =
                               FStarC_TypeChecker_Cfg.find_prim_step cfg fv in
                             (match uu___4 with
                              | FStar_Pervasives_Native.Some
                                  {
                                    FStarC_TypeChecker_Primops_Base.name =
                                      uu___5;
                                    FStarC_TypeChecker_Primops_Base.arity =
                                      uu___6;
                                    FStarC_TypeChecker_Primops_Base.univ_arity
                                      = uu___7;
                                    FStarC_TypeChecker_Primops_Base.auto_reflect
                                      = FStar_Pervasives_Native.Some n;
                                    FStarC_TypeChecker_Primops_Base.strong_reduction_ok
                                      = uu___8;
                                    FStarC_TypeChecker_Primops_Base.requires_binder_substitution
                                      = uu___9;
                                    FStarC_TypeChecker_Primops_Base.renorm_after
                                      = uu___10;
                                    FStarC_TypeChecker_Primops_Base.interpretation
                                      = uu___11;
                                    FStarC_TypeChecker_Primops_Base.interpretation_nbe
                                      = uu___12;_}
                                  when (FStarC_Compiler_List.length args) = n
                                  -> norm cfg env2 stack' t
                              | uu___5 -> fallback " (3)" ())
                         | uu___4 -> fallback " (4)" ()))
               | uu___1 -> fallback " (2)" ())
          | (App (env2, head, aq, r))::stack2 ->
              let t1 = FStarC_Syntax_Syntax.extend_app head (t, aq) r in
              rebuild cfg env2 stack2 t1
          | (CBVApp (env', head, aq, r))::stack2 ->
              let uu___ =
                let uu___1 =
                  let uu___2 =
                    let uu___3 =
                      let uu___4 =
                        let uu___5 = fresh_memo () in
                        (env1, t, uu___5, false) in
                      Clos uu___4 in
                    (uu___3, aq, (t.FStarC_Syntax_Syntax.pos)) in
                  Arg uu___2 in
                uu___1 :: stack2 in
              norm cfg env' uu___ head
          | (Match (env', asc_opt, branches1, lopt, cfg1, r))::stack2 ->
              let lopt1 =
                FStarC_Compiler_Util.map_option
                  (norm_residual_comp cfg1 env') lopt in
              (FStarC_TypeChecker_Cfg.log cfg1
                 (fun uu___1 ->
                    let uu___2 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_term t in
                    FStarC_Compiler_Util.print1
                      "Rebuilding with match, scrutinee is %s ...\n" uu___2);
               (let scrutinee_env = env1 in
                let env2 = env' in
                let scrutinee = t in
                let norm_and_rebuild_match uu___1 =
                  FStarC_TypeChecker_Cfg.log cfg1
                    (fun uu___3 ->
                       let uu___4 =
                         FStarC_Class_Show.show
                           FStarC_Syntax_Print.showable_term scrutinee in
                       let uu___5 =
                         let uu___6 =
                           FStarC_Compiler_List.map
                             (fun uu___7 ->
                                match uu___7 with
                                | (p, uu___8, uu___9) ->
                                    FStarC_Class_Show.show
                                      FStarC_Syntax_Print.showable_pat p)
                             branches1 in
                         FStarC_Compiler_String.concat "\n\t" uu___6 in
                       FStarC_Compiler_Util.print2
                         "match is irreducible: scrutinee=%s\nbranches=%s\n"
                         uu___4 uu___5);
                  (let whnf =
                     (cfg1.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weak
                       ||
                       (cfg1.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.hnf in
                   let cfg_exclude_zeta =
                     if
                       (cfg1.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.zeta_full
                     then cfg1
                     else
                       (let new_delta =
                          FStarC_Compiler_List.filter
                            (fun uu___4 ->
                               match uu___4 with
                               | FStarC_TypeChecker_Env.InliningDelta -> true
                               | FStarC_TypeChecker_Env.Eager_unfolding_only
                                   -> true
                               | uu___5 -> false)
                            cfg1.FStarC_TypeChecker_Cfg.delta_level in
                        let steps =
                          let uu___4 = cfg1.FStarC_TypeChecker_Cfg.steps in
                          {
                            FStarC_TypeChecker_Cfg.beta =
                              (uu___4.FStarC_TypeChecker_Cfg.beta);
                            FStarC_TypeChecker_Cfg.iota =
                              (uu___4.FStarC_TypeChecker_Cfg.iota);
                            FStarC_TypeChecker_Cfg.zeta = false;
                            FStarC_TypeChecker_Cfg.zeta_full =
                              (uu___4.FStarC_TypeChecker_Cfg.zeta_full);
                            FStarC_TypeChecker_Cfg.weak =
                              (uu___4.FStarC_TypeChecker_Cfg.weak);
                            FStarC_TypeChecker_Cfg.hnf =
                              (uu___4.FStarC_TypeChecker_Cfg.hnf);
                            FStarC_TypeChecker_Cfg.primops =
                              (uu___4.FStarC_TypeChecker_Cfg.primops);
                            FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets =
                              (uu___4.FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets);
                            FStarC_TypeChecker_Cfg.unfold_until =
                              FStar_Pervasives_Native.None;
                            FStarC_TypeChecker_Cfg.unfold_only =
                              FStar_Pervasives_Native.None;
                            FStarC_TypeChecker_Cfg.unfold_fully =
                              (uu___4.FStarC_TypeChecker_Cfg.unfold_fully);
                            FStarC_TypeChecker_Cfg.unfold_attr =
                              FStar_Pervasives_Native.None;
                            FStarC_TypeChecker_Cfg.unfold_qual =
                              FStar_Pervasives_Native.None;
                            FStarC_TypeChecker_Cfg.unfold_namespace =
                              FStar_Pervasives_Native.None;
                            FStarC_TypeChecker_Cfg.dont_unfold_attr =
                              FStar_Pervasives_Native.None;
                            FStarC_TypeChecker_Cfg.pure_subterms_within_computations
                              =
                              (uu___4.FStarC_TypeChecker_Cfg.pure_subterms_within_computations);
                            FStarC_TypeChecker_Cfg.simplify =
                              (uu___4.FStarC_TypeChecker_Cfg.simplify);
                            FStarC_TypeChecker_Cfg.erase_universes =
                              (uu___4.FStarC_TypeChecker_Cfg.erase_universes);
                            FStarC_TypeChecker_Cfg.allow_unbound_universes =
                              (uu___4.FStarC_TypeChecker_Cfg.allow_unbound_universes);
                            FStarC_TypeChecker_Cfg.reify_ =
                              (uu___4.FStarC_TypeChecker_Cfg.reify_);
                            FStarC_TypeChecker_Cfg.compress_uvars =
                              (uu___4.FStarC_TypeChecker_Cfg.compress_uvars);
                            FStarC_TypeChecker_Cfg.no_full_norm =
                              (uu___4.FStarC_TypeChecker_Cfg.no_full_norm);
                            FStarC_TypeChecker_Cfg.check_no_uvars =
                              (uu___4.FStarC_TypeChecker_Cfg.check_no_uvars);
                            FStarC_TypeChecker_Cfg.unmeta =
                              (uu___4.FStarC_TypeChecker_Cfg.unmeta);
                            FStarC_TypeChecker_Cfg.unascribe =
                              (uu___4.FStarC_TypeChecker_Cfg.unascribe);
                            FStarC_TypeChecker_Cfg.in_full_norm_request =
                              (uu___4.FStarC_TypeChecker_Cfg.in_full_norm_request);
                            FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee =
                              (uu___4.FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee);
                            FStarC_TypeChecker_Cfg.nbe_step =
                              (uu___4.FStarC_TypeChecker_Cfg.nbe_step);
                            FStarC_TypeChecker_Cfg.for_extraction =
                              (uu___4.FStarC_TypeChecker_Cfg.for_extraction);
                            FStarC_TypeChecker_Cfg.unrefine =
                              (uu___4.FStarC_TypeChecker_Cfg.unrefine);
                            FStarC_TypeChecker_Cfg.default_univs_to_zero =
                              (uu___4.FStarC_TypeChecker_Cfg.default_univs_to_zero);
                            FStarC_TypeChecker_Cfg.tactics =
                              (uu___4.FStarC_TypeChecker_Cfg.tactics)
                          } in
                        {
                          FStarC_TypeChecker_Cfg.steps = steps;
                          FStarC_TypeChecker_Cfg.tcenv =
                            (cfg1.FStarC_TypeChecker_Cfg.tcenv);
                          FStarC_TypeChecker_Cfg.debug =
                            (cfg1.FStarC_TypeChecker_Cfg.debug);
                          FStarC_TypeChecker_Cfg.delta_level = new_delta;
                          FStarC_TypeChecker_Cfg.primitive_steps =
                            (cfg1.FStarC_TypeChecker_Cfg.primitive_steps);
                          FStarC_TypeChecker_Cfg.strong = true;
                          FStarC_TypeChecker_Cfg.memoize_lazy =
                            (cfg1.FStarC_TypeChecker_Cfg.memoize_lazy);
                          FStarC_TypeChecker_Cfg.normalize_pure_lets =
                            (cfg1.FStarC_TypeChecker_Cfg.normalize_pure_lets);
                          FStarC_TypeChecker_Cfg.reifying =
                            (cfg1.FStarC_TypeChecker_Cfg.reifying);
                          FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg =
                            (cfg1.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
                        }) in
                   let norm_or_whnf env3 t1 =
                     if whnf
                     then closure_as_term cfg_exclude_zeta env3 t1
                     else norm cfg_exclude_zeta env3 [] t1 in
                   let rec norm_pat env3 p =
                     match p.FStarC_Syntax_Syntax.v with
                     | FStarC_Syntax_Syntax.Pat_constant uu___3 -> (p, env3)
                     | FStarC_Syntax_Syntax.Pat_cons (fv, us_opt, pats) ->
                         let us_opt1 =
                           if
                             (cfg1.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.erase_universes
                           then FStar_Pervasives_Native.None
                           else
                             (match us_opt with
                              | FStar_Pervasives_Native.None ->
                                  FStar_Pervasives_Native.None
                              | FStar_Pervasives_Native.Some us ->
                                  let uu___4 =
                                    FStarC_Compiler_List.map
                                      (norm_universe cfg1 env3) us in
                                  FStar_Pervasives_Native.Some uu___4) in
                         let uu___3 =
                           FStarC_Compiler_List.fold_left
                             (fun uu___4 ->
                                fun uu___5 ->
                                  match (uu___4, uu___5) with
                                  | ((pats1, env4), (p1, b)) ->
                                      let uu___6 = norm_pat env4 p1 in
                                      (match uu___6 with
                                       | (p2, env5) ->
                                           (((p2, b) :: pats1), env5)))
                             ([], env3) pats in
                         (match uu___3 with
                          | (pats1, env4) ->
                              ({
                                 FStarC_Syntax_Syntax.v =
                                   (FStarC_Syntax_Syntax.Pat_cons
                                      (fv, us_opt1,
                                        (FStarC_Compiler_List.rev pats1)));
                                 FStarC_Syntax_Syntax.p =
                                   (p.FStarC_Syntax_Syntax.p)
                               }, env4))
                     | FStarC_Syntax_Syntax.Pat_var x ->
                         let x1 =
                           let uu___3 =
                             norm_or_whnf env3 x.FStarC_Syntax_Syntax.sort in
                           {
                             FStarC_Syntax_Syntax.ppname =
                               (x.FStarC_Syntax_Syntax.ppname);
                             FStarC_Syntax_Syntax.index =
                               (x.FStarC_Syntax_Syntax.index);
                             FStarC_Syntax_Syntax.sort = uu___3
                           } in
                         let uu___3 = let uu___4 = dummy () in uu___4 :: env3 in
                         ({
                            FStarC_Syntax_Syntax.v =
                              (FStarC_Syntax_Syntax.Pat_var x1);
                            FStarC_Syntax_Syntax.p =
                              (p.FStarC_Syntax_Syntax.p)
                          }, uu___3)
                     | FStarC_Syntax_Syntax.Pat_dot_term eopt ->
                         let eopt1 =
                           FStarC_Compiler_Util.map_option
                             (norm_or_whnf env3) eopt in
                         ({
                            FStarC_Syntax_Syntax.v =
                              (FStarC_Syntax_Syntax.Pat_dot_term eopt1);
                            FStarC_Syntax_Syntax.p =
                              (p.FStarC_Syntax_Syntax.p)
                          }, env3) in
                   let norm_branches uu___3 =
                     match env2 with
                     | [] when whnf -> branches1
                     | uu___4 ->
                         FStarC_Compiler_List.map
                           (fun branch ->
                              let uu___5 =
                                FStarC_Syntax_Subst.open_branch branch in
                              match uu___5 with
                              | (p, wopt, e) ->
                                  let uu___6 = norm_pat env2 p in
                                  (match uu___6 with
                                   | (p1, env3) ->
                                       let wopt1 =
                                         match wopt with
                                         | FStar_Pervasives_Native.None ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some w ->
                                             let uu___7 = norm_or_whnf env3 w in
                                             FStar_Pervasives_Native.Some
                                               uu___7 in
                                       let e1 = norm_or_whnf env3 e in
                                       FStarC_Syntax_Util.branch
                                         (p1, wopt1, e1))) branches1 in
                   let maybe_commute_matches uu___3 =
                     let can_commute =
                       match branches1 with
                       | ({
                            FStarC_Syntax_Syntax.v =
                              FStarC_Syntax_Syntax.Pat_cons
                              (fv, uu___4, uu___5);
                            FStarC_Syntax_Syntax.p = uu___6;_},
                          uu___7, uu___8)::uu___9 ->
                           FStarC_TypeChecker_Env.fv_has_attr
                             cfg1.FStarC_TypeChecker_Cfg.tcenv fv
                             FStarC_Parser_Const.commute_nested_matches_lid
                       | uu___4 -> false in
                     let uu___4 =
                       let uu___5 = FStarC_Syntax_Util.unascribe scrutinee in
                       uu___5.FStarC_Syntax_Syntax.n in
                     match uu___4 with
                     | FStarC_Syntax_Syntax.Tm_match
                         { FStarC_Syntax_Syntax.scrutinee = sc0;
                           FStarC_Syntax_Syntax.ret_opt = asc_opt0;
                           FStarC_Syntax_Syntax.brs = branches0;
                           FStarC_Syntax_Syntax.rc_opt1 = lopt0;_}
                         when can_commute ->
                         let reduce_branch b =
                           let stack3 =
                             [Match
                                (env', asc_opt, branches1, lopt1, cfg1, r)] in
                           let uu___5 = FStarC_Syntax_Subst.open_branch b in
                           match uu___5 with
                           | (p, wopt, e) ->
                               let uu___6 = norm_pat scrutinee_env p in
                               (match uu___6 with
                                | (p1, branch_env) ->
                                    let wopt1 =
                                      match wopt with
                                      | FStar_Pervasives_Native.None ->
                                          FStar_Pervasives_Native.None
                                      | FStar_Pervasives_Native.Some w ->
                                          let uu___7 =
                                            norm_or_whnf branch_env w in
                                          FStar_Pervasives_Native.Some uu___7 in
                                    let e1 = norm cfg1 branch_env stack3 e in
                                    FStarC_Syntax_Util.branch (p1, wopt1, e1)) in
                         let branches01 =
                           FStarC_Compiler_List.map reduce_branch branches0 in
                         let uu___5 =
                           FStarC_Syntax_Syntax.mk
                             (FStarC_Syntax_Syntax.Tm_match
                                {
                                  FStarC_Syntax_Syntax.scrutinee = sc0;
                                  FStarC_Syntax_Syntax.ret_opt = asc_opt0;
                                  FStarC_Syntax_Syntax.brs = branches01;
                                  FStarC_Syntax_Syntax.rc_opt1 = lopt0
                                }) r in
                         rebuild cfg1 env2 stack2 uu___5
                     | uu___5 ->
                         let scrutinee1 =
                           let uu___6 =
                             ((((cfg1.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.iota
                                  &&
                                  (Prims.op_Negation
                                     (cfg1.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weak))
                                 &&
                                 (Prims.op_Negation
                                    (cfg1.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.compress_uvars))
                                &&
                                (cfg1.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee)
                               && (maybe_weakly_reduced scrutinee) in
                           if uu___6
                           then
                             norm
                               {
                                 FStarC_TypeChecker_Cfg.steps =
                                   (let uu___7 =
                                      cfg1.FStarC_TypeChecker_Cfg.steps in
                                    {
                                      FStarC_TypeChecker_Cfg.beta =
                                        (uu___7.FStarC_TypeChecker_Cfg.beta);
                                      FStarC_TypeChecker_Cfg.iota =
                                        (uu___7.FStarC_TypeChecker_Cfg.iota);
                                      FStarC_TypeChecker_Cfg.zeta =
                                        (uu___7.FStarC_TypeChecker_Cfg.zeta);
                                      FStarC_TypeChecker_Cfg.zeta_full =
                                        (uu___7.FStarC_TypeChecker_Cfg.zeta_full);
                                      FStarC_TypeChecker_Cfg.weak =
                                        (uu___7.FStarC_TypeChecker_Cfg.weak);
                                      FStarC_TypeChecker_Cfg.hnf =
                                        (uu___7.FStarC_TypeChecker_Cfg.hnf);
                                      FStarC_TypeChecker_Cfg.primops =
                                        (uu___7.FStarC_TypeChecker_Cfg.primops);
                                      FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets
                                        =
                                        (uu___7.FStarC_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                      FStarC_TypeChecker_Cfg.unfold_until =
                                        (uu___7.FStarC_TypeChecker_Cfg.unfold_until);
                                      FStarC_TypeChecker_Cfg.unfold_only =
                                        (uu___7.FStarC_TypeChecker_Cfg.unfold_only);
                                      FStarC_TypeChecker_Cfg.unfold_fully =
                                        (uu___7.FStarC_TypeChecker_Cfg.unfold_fully);
                                      FStarC_TypeChecker_Cfg.unfold_attr =
                                        (uu___7.FStarC_TypeChecker_Cfg.unfold_attr);
                                      FStarC_TypeChecker_Cfg.unfold_qual =
                                        (uu___7.FStarC_TypeChecker_Cfg.unfold_qual);
                                      FStarC_TypeChecker_Cfg.unfold_namespace
                                        =
                                        (uu___7.FStarC_TypeChecker_Cfg.unfold_namespace);
                                      FStarC_TypeChecker_Cfg.dont_unfold_attr
                                        =
                                        (uu___7.FStarC_TypeChecker_Cfg.dont_unfold_attr);
                                      FStarC_TypeChecker_Cfg.pure_subterms_within_computations
                                        =
                                        (uu___7.FStarC_TypeChecker_Cfg.pure_subterms_within_computations);
                                      FStarC_TypeChecker_Cfg.simplify =
                                        (uu___7.FStarC_TypeChecker_Cfg.simplify);
                                      FStarC_TypeChecker_Cfg.erase_universes
                                        =
                                        (uu___7.FStarC_TypeChecker_Cfg.erase_universes);
                                      FStarC_TypeChecker_Cfg.allow_unbound_universes
                                        =
                                        (uu___7.FStarC_TypeChecker_Cfg.allow_unbound_universes);
                                      FStarC_TypeChecker_Cfg.reify_ =
                                        (uu___7.FStarC_TypeChecker_Cfg.reify_);
                                      FStarC_TypeChecker_Cfg.compress_uvars =
                                        (uu___7.FStarC_TypeChecker_Cfg.compress_uvars);
                                      FStarC_TypeChecker_Cfg.no_full_norm =
                                        (uu___7.FStarC_TypeChecker_Cfg.no_full_norm);
                                      FStarC_TypeChecker_Cfg.check_no_uvars =
                                        (uu___7.FStarC_TypeChecker_Cfg.check_no_uvars);
                                      FStarC_TypeChecker_Cfg.unmeta =
                                        (uu___7.FStarC_TypeChecker_Cfg.unmeta);
                                      FStarC_TypeChecker_Cfg.unascribe =
                                        (uu___7.FStarC_TypeChecker_Cfg.unascribe);
                                      FStarC_TypeChecker_Cfg.in_full_norm_request
                                        =
                                        (uu___7.FStarC_TypeChecker_Cfg.in_full_norm_request);
                                      FStarC_TypeChecker_Cfg.weakly_reduce_scrutinee
                                        = false;
                                      FStarC_TypeChecker_Cfg.nbe_step =
                                        (uu___7.FStarC_TypeChecker_Cfg.nbe_step);
                                      FStarC_TypeChecker_Cfg.for_extraction =
                                        (uu___7.FStarC_TypeChecker_Cfg.for_extraction);
                                      FStarC_TypeChecker_Cfg.unrefine =
                                        (uu___7.FStarC_TypeChecker_Cfg.unrefine);
                                      FStarC_TypeChecker_Cfg.default_univs_to_zero
                                        =
                                        (uu___7.FStarC_TypeChecker_Cfg.default_univs_to_zero);
                                      FStarC_TypeChecker_Cfg.tactics =
                                        (uu___7.FStarC_TypeChecker_Cfg.tactics)
                                    });
                                 FStarC_TypeChecker_Cfg.tcenv =
                                   (cfg1.FStarC_TypeChecker_Cfg.tcenv);
                                 FStarC_TypeChecker_Cfg.debug =
                                   (cfg1.FStarC_TypeChecker_Cfg.debug);
                                 FStarC_TypeChecker_Cfg.delta_level =
                                   (cfg1.FStarC_TypeChecker_Cfg.delta_level);
                                 FStarC_TypeChecker_Cfg.primitive_steps =
                                   (cfg1.FStarC_TypeChecker_Cfg.primitive_steps);
                                 FStarC_TypeChecker_Cfg.strong =
                                   (cfg1.FStarC_TypeChecker_Cfg.strong);
                                 FStarC_TypeChecker_Cfg.memoize_lazy =
                                   (cfg1.FStarC_TypeChecker_Cfg.memoize_lazy);
                                 FStarC_TypeChecker_Cfg.normalize_pure_lets =
                                   (cfg1.FStarC_TypeChecker_Cfg.normalize_pure_lets);
                                 FStarC_TypeChecker_Cfg.reifying =
                                   (cfg1.FStarC_TypeChecker_Cfg.reifying);
                                 FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg
                                   =
                                   (cfg1.FStarC_TypeChecker_Cfg.compat_memo_ignore_cfg)
                               } scrutinee_env [] scrutinee
                           else scrutinee in
                         let asc_opt1 = norm_match_returns cfg1 env2 asc_opt in
                         let branches2 = norm_branches () in
                         let uu___6 =
                           FStarC_Syntax_Syntax.mk
                             (FStarC_Syntax_Syntax.Tm_match
                                {
                                  FStarC_Syntax_Syntax.scrutinee = scrutinee1;
                                  FStarC_Syntax_Syntax.ret_opt = asc_opt1;
                                  FStarC_Syntax_Syntax.brs = branches2;
                                  FStarC_Syntax_Syntax.rc_opt1 = lopt1
                                }) r in
                         rebuild cfg1 env2 stack2 uu___6 in
                   maybe_commute_matches ()) in
                let rec is_cons head =
                  let uu___1 =
                    let uu___2 = FStarC_Syntax_Subst.compress head in
                    uu___2.FStarC_Syntax_Syntax.n in
                  match uu___1 with
                  | FStarC_Syntax_Syntax.Tm_uinst (h, uu___2) -> is_cons h
                  | FStarC_Syntax_Syntax.Tm_constant uu___2 -> true
                  | FStarC_Syntax_Syntax.Tm_fvar
                      { FStarC_Syntax_Syntax.fv_name = uu___2;
                        FStarC_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStarC_Syntax_Syntax.Data_ctor);_}
                      -> true
                  | FStarC_Syntax_Syntax.Tm_fvar
                      { FStarC_Syntax_Syntax.fv_name = uu___2;
                        FStarC_Syntax_Syntax.fv_qual =
                          FStar_Pervasives_Native.Some
                          (FStarC_Syntax_Syntax.Record_ctor uu___3);_}
                      -> true
                  | uu___2 -> false in
                let guard_when_clause wopt b rest =
                  match wopt with
                  | FStar_Pervasives_Native.None -> b
                  | FStar_Pervasives_Native.Some w ->
                      let then_branch = b in
                      let else_branch =
                        FStarC_Syntax_Syntax.mk
                          (FStarC_Syntax_Syntax.Tm_match
                             {
                               FStarC_Syntax_Syntax.scrutinee = scrutinee;
                               FStarC_Syntax_Syntax.ret_opt = asc_opt;
                               FStarC_Syntax_Syntax.brs = rest;
                               FStarC_Syntax_Syntax.rc_opt1 = lopt1
                             }) r in
                      FStarC_Syntax_Util.if_then_else w then_branch
                        else_branch in
                let rec matches_pat scrutinee_orig p =
                  let scrutinee1 = FStarC_Syntax_Util.unmeta scrutinee_orig in
                  let scrutinee2 = FStarC_Syntax_Util.unlazy scrutinee1 in
                  let uu___1 = FStarC_Syntax_Util.head_and_args scrutinee2 in
                  match uu___1 with
                  | (head, args) ->
                      (match p.FStarC_Syntax_Syntax.v with
                       | FStarC_Syntax_Syntax.Pat_var bv ->
                           FStar_Pervasives.Inl [(bv, scrutinee_orig)]
                       | FStarC_Syntax_Syntax.Pat_dot_term uu___2 ->
                           FStar_Pervasives.Inl []
                       | FStarC_Syntax_Syntax.Pat_constant s ->
                           (match scrutinee2.FStarC_Syntax_Syntax.n with
                            | FStarC_Syntax_Syntax.Tm_constant s' when
                                FStarC_Const.eq_const s s' ->
                                FStar_Pervasives.Inl []
                            | uu___2 ->
                                let uu___3 =
                                  let uu___4 = is_cons head in
                                  Prims.op_Negation uu___4 in
                                FStar_Pervasives.Inr uu___3)
                       | FStarC_Syntax_Syntax.Pat_cons (fv, uu___2, arg_pats)
                           ->
                           let uu___3 =
                             let uu___4 = FStarC_Syntax_Util.un_uinst head in
                             uu___4.FStarC_Syntax_Syntax.n in
                           (match uu___3 with
                            | FStarC_Syntax_Syntax.Tm_fvar fv' when
                                FStarC_Syntax_Syntax.fv_eq fv fv' ->
                                matches_args [] args arg_pats
                            | uu___4 ->
                                let uu___5 =
                                  let uu___6 = is_cons head in
                                  Prims.op_Negation uu___6 in
                                FStar_Pervasives.Inr uu___5))
                and matches_args out a p =
                  match (a, p) with
                  | ([], []) -> FStar_Pervasives.Inl out
                  | ((t1, uu___1)::rest_a, (p1, uu___2)::rest_p) ->
                      let uu___3 = matches_pat t1 p1 in
                      (match uu___3 with
                       | FStar_Pervasives.Inl s ->
                           matches_args (FStarC_Compiler_List.op_At out s)
                             rest_a rest_p
                       | m -> m)
                  | uu___1 -> FStar_Pervasives.Inr false in
                let rec matches scrutinee1 p =
                  match p with
                  | [] -> norm_and_rebuild_match ()
                  | (p1, wopt, b)::rest ->
                      let uu___1 = matches_pat scrutinee1 p1 in
                      (match uu___1 with
                       | FStar_Pervasives.Inr (false) ->
                           matches scrutinee1 rest
                       | FStar_Pervasives.Inr (true) ->
                           norm_and_rebuild_match ()
                       | FStar_Pervasives.Inl s ->
                           (FStarC_TypeChecker_Cfg.log cfg1
                              (fun uu___3 ->
                                 let uu___4 =
                                   FStarC_Class_Show.show
                                     FStarC_Syntax_Print.showable_pat p1 in
                                 let uu___5 =
                                   let uu___6 =
                                     FStarC_Compiler_List.map
                                       (fun uu___7 ->
                                          match uu___7 with
                                          | (uu___8, t1) ->
                                              FStarC_Class_Show.show
                                                FStarC_Syntax_Print.showable_term
                                                t1) s in
                                   FStarC_Compiler_String.concat "; " uu___6 in
                                 FStarC_Compiler_Util.print2
                                   "Matches pattern %s with subst = %s\n"
                                   uu___4 uu___5);
                            (let env0 = env2 in
                             let env3 =
                               FStarC_Compiler_List.fold_left
                                 (fun env4 ->
                                    fun uu___3 ->
                                      match uu___3 with
                                      | (bv, t1) ->
                                          let uu___4 =
                                            let uu___5 =
                                              let uu___6 =
                                                FStarC_Syntax_Syntax.mk_binder
                                                  bv in
                                              FStar_Pervasives_Native.Some
                                                uu___6 in
                                            let uu___6 =
                                              let uu___7 =
                                                let uu___8 =
                                                  FStarC_Compiler_Util.mk_ref
                                                    (if
                                                       (cfg1.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.hnf
                                                     then
                                                       FStar_Pervasives_Native.None
                                                     else
                                                       FStar_Pervasives_Native.Some
                                                         (cfg1, ([], t1))) in
                                                ([], t1, uu___8, false) in
                                              Clos uu___7 in
                                            let uu___7 = fresh_memo () in
                                            (uu___5, uu___6, uu___7) in
                                          uu___4 :: env4) env2 s in
                             let uu___3 = guard_when_clause wopt b rest in
                             norm cfg1 env3 stack2 uu___3))) in
                if
                  (cfg1.FStarC_TypeChecker_Cfg.steps).FStarC_TypeChecker_Cfg.iota
                then matches scrutinee branches1
                else norm_and_rebuild_match ()))
and (norm_match_returns :
  FStarC_TypeChecker_Cfg.cfg ->
    env ->
      FStarC_Syntax_Syntax.match_returns_ascription
        FStar_Pervasives_Native.option ->
        (FStarC_Syntax_Syntax.binder *
          ((FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax,
          FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax)
          FStar_Pervasives.either * FStarC_Syntax_Syntax.term'
          FStarC_Syntax_Syntax.syntax FStar_Pervasives_Native.option *
          Prims.bool)) FStar_Pervasives_Native.option)
  =
  fun cfg ->
    fun env1 ->
      fun ret_opt ->
        match ret_opt with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (b, asc) ->
            let b1 = norm_binder cfg env1 b in
            let uu___ = FStarC_Syntax_Subst.open_ascription [b1] asc in
            (match uu___ with
             | (subst, asc1) ->
                 let asc2 =
                   let uu___1 = let uu___2 = dummy () in uu___2 :: env1 in
                   norm_ascription cfg uu___1 asc1 in
                 let uu___1 =
                   let uu___2 =
                     FStarC_Syntax_Subst.close_ascription subst asc2 in
                   (b1, uu___2) in
                 FStar_Pervasives_Native.Some uu___1)
and (norm_ascription :
  FStarC_TypeChecker_Cfg.cfg ->
    env ->
      ((FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax,
        FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax)
        FStar_Pervasives.either * FStarC_Syntax_Syntax.term'
        FStarC_Syntax_Syntax.syntax FStar_Pervasives_Native.option *
        Prims.bool) ->
        ((FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax,
          FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax)
          FStar_Pervasives.either * FStarC_Syntax_Syntax.term'
          FStarC_Syntax_Syntax.syntax FStar_Pervasives_Native.option *
          Prims.bool))
  =
  fun cfg ->
    fun env1 ->
      fun uu___ ->
        match uu___ with
        | (tc, tacopt, use_eq) ->
            let uu___1 =
              match tc with
              | FStar_Pervasives.Inl t ->
                  let uu___2 = norm cfg env1 [] t in
                  FStar_Pervasives.Inl uu___2
              | FStar_Pervasives.Inr c ->
                  let uu___2 = norm_comp cfg env1 c in
                  FStar_Pervasives.Inr uu___2 in
            let uu___2 =
              FStarC_Compiler_Util.map_opt tacopt (norm cfg env1 []) in
            (uu___1, uu___2, use_eq)
and (norm_residual_comp :
  FStarC_TypeChecker_Cfg.cfg ->
    env ->
      FStarC_Syntax_Syntax.residual_comp ->
        FStarC_Syntax_Syntax.residual_comp)
  =
  fun cfg ->
    fun env1 ->
      fun rc ->
        let uu___ =
          FStarC_Compiler_Util.map_option (closure_as_term cfg env1)
            rc.FStarC_Syntax_Syntax.residual_typ in
        {
          FStarC_Syntax_Syntax.residual_effect =
            (rc.FStarC_Syntax_Syntax.residual_effect);
          FStarC_Syntax_Syntax.residual_typ = uu___;
          FStarC_Syntax_Syntax.residual_flags =
            (rc.FStarC_Syntax_Syntax.residual_flags)
        }
let (reflection_env_hook :
  FStarC_TypeChecker_Env.env FStar_Pervasives_Native.option
    FStarC_Compiler_Effect.ref)
  = FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None
let (normalize_with_primitive_steps :
  FStarC_TypeChecker_Primops_Base.primitive_step Prims.list ->
    FStarC_TypeChecker_Env.steps ->
      FStarC_TypeChecker_Env.env ->
        FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun ps ->
    fun s ->
      fun e ->
        fun t ->
          let is_nbe = is_nbe_request s in
          let maybe_nbe = if is_nbe then " (NBE)" else "" in
          FStarC_Errors.with_ctx
            (Prims.strcat "While normalizing a term" maybe_nbe)
            (fun uu___ ->
               let uu___1 =
                 let uu___2 =
                   let uu___3 = FStarC_TypeChecker_Env.current_module e in
                   FStarC_Ident.string_of_lid uu___3 in
                 FStar_Pervasives_Native.Some uu___2 in
               FStarC_Profiling.profile
                 (fun uu___2 ->
                    let c = FStarC_TypeChecker_Cfg.config' ps s e in
                    FStarC_Compiler_Effect.op_Colon_Equals
                      reflection_env_hook (FStar_Pervasives_Native.Some e);
                    FStarC_Compiler_Effect.op_Colon_Equals
                      FStarC_TypeChecker_Normalize_Unfolding.plugin_unfold_warn_ctr
                      (Prims.of_int (10));
                    FStarC_TypeChecker_Cfg.log_top c
                      (fun uu___6 ->
                         let uu___7 =
                           FStarC_Class_Show.show
                             FStarC_Syntax_Print.showable_term t in
                         FStarC_Compiler_Util.print2
                           "\nStarting normalizer%s for (%s) {\n" maybe_nbe
                           uu___7);
                    FStarC_TypeChecker_Cfg.log_top c
                      (fun uu___7 ->
                         let uu___8 =
                           FStarC_Class_Show.show
                             FStarC_TypeChecker_Cfg.showable_cfg c in
                         FStarC_Compiler_Util.print1 ">>> cfg = %s\n" uu___8);
                    FStarC_Defensive.def_check_scoped
                      FStarC_TypeChecker_Env.hasBinders_env
                      FStarC_Class_Binders.hasNames_term
                      FStarC_Syntax_Print.pretty_term
                      t.FStarC_Syntax_Syntax.pos
                      "normalize_with_primitive_steps call" e t;
                    (let uu___8 =
                       FStarC_Compiler_Util.record_time
                         (fun uu___9 ->
                            if is_nbe then nbe_eval c s t else norm c [] [] t) in
                     match uu___8 with
                     | (r, ms) ->
                         (FStarC_TypeChecker_Cfg.log_top c
                            (fun uu___10 ->
                               let uu___11 =
                                 FStarC_Class_Show.show
                                   FStarC_Syntax_Print.showable_term r in
                               let uu___12 =
                                 FStarC_Class_Show.show
                                   FStarC_Class_Show.showable_int ms in
                               FStarC_Compiler_Util.print3
                                 "}\nNormalization%s result = (%s) in %s ms\n"
                                 maybe_nbe uu___11 uu___12);
                          r))) uu___1
                 "FStarC.TypeChecker.Normalize.normalize_with_primitive_steps")
let (normalize :
  FStarC_TypeChecker_Env.steps ->
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun s ->
    fun e ->
      fun t ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_TypeChecker_Env.current_module e in
            FStarC_Ident.string_of_lid uu___2 in
          FStar_Pervasives_Native.Some uu___1 in
        FStarC_Profiling.profile
          (fun uu___1 -> normalize_with_primitive_steps [] s e t) uu___
          "FStarC.TypeChecker.Normalize.normalize"
let (normalize_comp :
  FStarC_TypeChecker_Env.steps ->
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.comp -> FStarC_Syntax_Syntax.comp)
  =
  fun s ->
    fun e ->
      fun c ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_TypeChecker_Env.current_module e in
            FStarC_Ident.string_of_lid uu___2 in
          FStar_Pervasives_Native.Some uu___1 in
        FStarC_Profiling.profile
          (fun uu___1 ->
             let cfg = FStarC_TypeChecker_Cfg.config s e in
             FStarC_Compiler_Effect.op_Colon_Equals reflection_env_hook
               (FStar_Pervasives_Native.Some e);
             FStarC_Compiler_Effect.op_Colon_Equals
               FStarC_TypeChecker_Normalize_Unfolding.plugin_unfold_warn_ctr
               (Prims.of_int (10));
             FStarC_TypeChecker_Cfg.log_top cfg
               (fun uu___5 ->
                  let uu___6 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_comp
                      c in
                  FStarC_Compiler_Util.print1
                    "Starting normalizer for computation (%s) {\n" uu___6);
             FStarC_TypeChecker_Cfg.log_top cfg
               (fun uu___6 ->
                  let uu___7 =
                    FStarC_Class_Show.show
                      FStarC_TypeChecker_Cfg.showable_cfg cfg in
                  FStarC_Compiler_Util.print1 ">>> cfg = %s\n" uu___7);
             FStarC_Defensive.def_check_scoped
               FStarC_TypeChecker_Env.hasBinders_env
               FStarC_Class_Binders.hasNames_comp
               FStarC_Syntax_Print.pretty_comp c.FStarC_Syntax_Syntax.pos
               "normalize_comp call" e c;
             (let uu___7 =
                FStarC_Errors.with_ctx "While normalizing a computation type"
                  (fun uu___8 ->
                     FStarC_Compiler_Util.record_time
                       (fun uu___9 -> norm_comp cfg [] c)) in
              match uu___7 with
              | (c1, ms) ->
                  (FStarC_TypeChecker_Cfg.log_top cfg
                     (fun uu___9 ->
                        let uu___10 =
                          FStarC_Class_Show.show
                            FStarC_Syntax_Print.showable_comp c1 in
                        let uu___11 =
                          FStarC_Class_Show.show
                            FStarC_Class_Show.showable_int ms in
                        FStarC_Compiler_Util.print2
                          "}\nNormalization result = (%s) in %s ms\n" uu___10
                          uu___11);
                   c1))) uu___ "FStarC.TypeChecker.Normalize.normalize_comp"
let (normalize_universe :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.universe -> FStarC_Syntax_Syntax.universe)
  =
  fun env1 ->
    fun u ->
      FStarC_Errors.with_ctx "While normalizing a universe level"
        (fun uu___ ->
           let uu___1 = FStarC_TypeChecker_Cfg.config [] env1 in
           norm_universe uu___1 [] u)
let (non_info_norm :
  FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun env1 ->
    fun t ->
      let steps =
        [FStarC_TypeChecker_Env.UnfoldUntil
           FStarC_Syntax_Syntax.delta_constant;
        FStarC_TypeChecker_Env.AllowUnboundUniverses;
        FStarC_TypeChecker_Env.EraseUniverses;
        FStarC_TypeChecker_Env.HNF;
        FStarC_TypeChecker_Env.Unascribe;
        FStarC_TypeChecker_Env.ForExtraction] in
      let uu___ = normalize steps env1 t in
      FStarC_TypeChecker_Env.non_informative env1 uu___
let (maybe_promote_t :
  FStarC_TypeChecker_Env.env ->
    Prims.bool -> FStarC_Syntax_Syntax.term -> Prims.bool)
  =
  fun env1 ->
    fun non_informative_only ->
      fun t ->
        (Prims.op_Negation non_informative_only) || (non_info_norm env1 t)
let (ghost_to_pure_aux :
  FStarC_TypeChecker_Env.env ->
    Prims.bool ->
      FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax ->
        FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax)
  =
  fun env1 ->
    fun non_informative_only ->
      fun c ->
        match c.FStarC_Syntax_Syntax.n with
        | FStarC_Syntax_Syntax.Total uu___ -> c
        | FStarC_Syntax_Syntax.GTotal t ->
            let uu___ = maybe_promote_t env1 non_informative_only t in
            if uu___
            then
              {
                FStarC_Syntax_Syntax.n = (FStarC_Syntax_Syntax.Total t);
                FStarC_Syntax_Syntax.pos = (c.FStarC_Syntax_Syntax.pos);
                FStarC_Syntax_Syntax.vars = (c.FStarC_Syntax_Syntax.vars);
                FStarC_Syntax_Syntax.hash_code =
                  (c.FStarC_Syntax_Syntax.hash_code)
              }
            else c
        | FStarC_Syntax_Syntax.Comp ct ->
            let l =
              FStarC_TypeChecker_Env.norm_eff_name env1
                ct.FStarC_Syntax_Syntax.effect_name in
            let uu___ =
              (FStarC_Syntax_Util.is_ghost_effect l) &&
                (maybe_promote_t env1 non_informative_only
                   ct.FStarC_Syntax_Syntax.result_typ) in
            if uu___
            then
              let ct1 =
                let uu___1 =
                  downgrade_ghost_effect_name
                    ct.FStarC_Syntax_Syntax.effect_name in
                match uu___1 with
                | FStar_Pervasives_Native.Some pure_eff ->
                    let flags =
                      let uu___2 =
                        FStarC_Ident.lid_equals pure_eff
                          FStarC_Parser_Const.effect_Tot_lid in
                      if uu___2
                      then FStarC_Syntax_Syntax.TOTAL ::
                        (ct.FStarC_Syntax_Syntax.flags)
                      else ct.FStarC_Syntax_Syntax.flags in
                    {
                      FStarC_Syntax_Syntax.comp_univs =
                        (ct.FStarC_Syntax_Syntax.comp_univs);
                      FStarC_Syntax_Syntax.effect_name = pure_eff;
                      FStarC_Syntax_Syntax.result_typ =
                        (ct.FStarC_Syntax_Syntax.result_typ);
                      FStarC_Syntax_Syntax.effect_args =
                        (ct.FStarC_Syntax_Syntax.effect_args);
                      FStarC_Syntax_Syntax.flags = flags
                    }
                | FStar_Pervasives_Native.None ->
                    let ct2 =
                      FStarC_TypeChecker_Env.unfold_effect_abbrev env1 c in
                    {
                      FStarC_Syntax_Syntax.comp_univs =
                        (ct2.FStarC_Syntax_Syntax.comp_univs);
                      FStarC_Syntax_Syntax.effect_name =
                        FStarC_Parser_Const.effect_PURE_lid;
                      FStarC_Syntax_Syntax.result_typ =
                        (ct2.FStarC_Syntax_Syntax.result_typ);
                      FStarC_Syntax_Syntax.effect_args =
                        (ct2.FStarC_Syntax_Syntax.effect_args);
                      FStarC_Syntax_Syntax.flags =
                        (ct2.FStarC_Syntax_Syntax.flags)
                    } in
              {
                FStarC_Syntax_Syntax.n = (FStarC_Syntax_Syntax.Comp ct1);
                FStarC_Syntax_Syntax.pos = (c.FStarC_Syntax_Syntax.pos);
                FStarC_Syntax_Syntax.vars = (c.FStarC_Syntax_Syntax.vars);
                FStarC_Syntax_Syntax.hash_code =
                  (c.FStarC_Syntax_Syntax.hash_code)
              }
            else c
        | uu___ -> c
let (ghost_to_pure_lcomp_aux :
  FStarC_TypeChecker_Env.env ->
    Prims.bool ->
      FStarC_TypeChecker_Common.lcomp -> FStarC_TypeChecker_Common.lcomp)
  =
  fun env1 ->
    fun non_informative_only ->
      fun lc ->
        let uu___ =
          (FStarC_Syntax_Util.is_ghost_effect
             lc.FStarC_TypeChecker_Common.eff_name)
            &&
            (maybe_promote_t env1 non_informative_only
               lc.FStarC_TypeChecker_Common.res_typ) in
        if uu___
        then
          let uu___1 =
            downgrade_ghost_effect_name lc.FStarC_TypeChecker_Common.eff_name in
          match uu___1 with
          | FStar_Pervasives_Native.Some pure_eff ->
              let uu___2 =
                FStarC_TypeChecker_Common.apply_lcomp
                  (ghost_to_pure_aux env1 non_informative_only) (fun g -> g)
                  lc in
              {
                FStarC_TypeChecker_Common.eff_name = pure_eff;
                FStarC_TypeChecker_Common.res_typ =
                  (uu___2.FStarC_TypeChecker_Common.res_typ);
                FStarC_TypeChecker_Common.cflags =
                  (uu___2.FStarC_TypeChecker_Common.cflags);
                FStarC_TypeChecker_Common.comp_thunk =
                  (uu___2.FStarC_TypeChecker_Common.comp_thunk)
              }
          | FStar_Pervasives_Native.None -> lc
        else lc
let (maybe_ghost_to_pure :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.comp -> FStarC_Syntax_Syntax.comp)
  = fun env1 -> fun c -> ghost_to_pure_aux env1 true c
let (maybe_ghost_to_pure_lcomp :
  FStarC_TypeChecker_Env.env ->
    FStarC_TypeChecker_Common.lcomp -> FStarC_TypeChecker_Common.lcomp)
  = fun env1 -> fun lc -> ghost_to_pure_lcomp_aux env1 true lc
let (ghost_to_pure :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax)
  = fun env1 -> fun c -> ghost_to_pure_aux env1 false c
let (ghost_to_pure_lcomp :
  FStarC_TypeChecker_Env.env ->
    FStarC_TypeChecker_Common.lcomp -> FStarC_TypeChecker_Common.lcomp)
  = fun env1 -> fun lc -> ghost_to_pure_lcomp_aux env1 false lc
let (ghost_to_pure2 :
  FStarC_TypeChecker_Env.env ->
    (FStarC_Syntax_Syntax.comp * FStarC_Syntax_Syntax.comp) ->
      (FStarC_Syntax_Syntax.comp * FStarC_Syntax_Syntax.comp))
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
                 FStarC_TypeChecker_Env.norm_eff_name env1
                   (FStarC_Syntax_Util.comp_effect_name c11) in
               let c2_eff =
                 FStarC_TypeChecker_Env.norm_eff_name env1
                   (FStarC_Syntax_Util.comp_effect_name c21) in
               let uu___2 = FStarC_Ident.lid_equals c1_eff c2_eff in
               if uu___2
               then (c11, c21)
               else
                 (let c1_erasable =
                    FStarC_TypeChecker_Env.is_erasable_effect env1 c1_eff in
                  let c2_erasable =
                    FStarC_TypeChecker_Env.is_erasable_effect env1 c2_eff in
                  let uu___4 =
                    c1_erasable &&
                      (FStarC_Ident.lid_equals c2_eff
                         FStarC_Parser_Const.effect_GHOST_lid) in
                  if uu___4
                  then let uu___5 = ghost_to_pure env1 c21 in (c11, uu___5)
                  else
                    (let uu___6 =
                       c2_erasable &&
                         (FStarC_Ident.lid_equals c1_eff
                            FStarC_Parser_Const.effect_GHOST_lid) in
                     if uu___6
                     then
                       let uu___7 = ghost_to_pure env1 c11 in (uu___7, c21)
                     else (c11, c21))))
let (ghost_to_pure_lcomp2 :
  FStarC_TypeChecker_Env.env ->
    (FStarC_TypeChecker_Common.lcomp * FStarC_TypeChecker_Common.lcomp) ->
      (FStarC_TypeChecker_Common.lcomp * FStarC_TypeChecker_Common.lcomp))
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
                 FStarC_TypeChecker_Env.norm_eff_name env1
                   lc11.FStarC_TypeChecker_Common.eff_name in
               let lc2_eff =
                 FStarC_TypeChecker_Env.norm_eff_name env1
                   lc21.FStarC_TypeChecker_Common.eff_name in
               let uu___2 = FStarC_Ident.lid_equals lc1_eff lc2_eff in
               if uu___2
               then (lc11, lc21)
               else
                 (let lc1_erasable =
                    FStarC_TypeChecker_Env.is_erasable_effect env1 lc1_eff in
                  let lc2_erasable =
                    FStarC_TypeChecker_Env.is_erasable_effect env1 lc2_eff in
                  let uu___4 =
                    lc1_erasable &&
                      (FStarC_Ident.lid_equals lc2_eff
                         FStarC_Parser_Const.effect_GHOST_lid) in
                  if uu___4
                  then
                    let uu___5 = ghost_to_pure_lcomp env1 lc21 in
                    (lc11, uu___5)
                  else
                    (let uu___6 =
                       lc2_erasable &&
                         (FStarC_Ident.lid_equals lc1_eff
                            FStarC_Parser_Const.effect_GHOST_lid) in
                     if uu___6
                     then
                       let uu___7 = ghost_to_pure_lcomp env1 lc11 in
                       (uu___7, lc21)
                     else (lc11, lc21))))
let (warn_norm_failure :
  FStarC_Compiler_Range_Type.range -> Prims.exn -> unit) =
  fun r ->
    fun e ->
      let uu___ =
        let uu___1 = FStarC_Compiler_Util.message_of_exn e in
        FStarC_Compiler_Util.format1 "Normalization failed with error %s\n"
          uu___1 in
      FStarC_Errors.log_issue FStarC_Class_HasRange.hasRange_range r
        FStarC_Errors_Codes.Warning_NormalizationFailure ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
        (Obj.magic uu___)
let (term_to_doc :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term -> FStarC_Pprint.document)
  =
  fun env1 ->
    fun t ->
      let t1 =
        try
          (fun uu___ ->
             match () with
             | () ->
                 normalize [FStarC_TypeChecker_Env.AllowUnboundUniverses]
                   env1 t) ()
        with
        | uu___ -> (warn_norm_failure t.FStarC_Syntax_Syntax.pos uu___; t) in
      let uu___ =
        FStarC_Syntax_DsEnv.set_current_module
          env1.FStarC_TypeChecker_Env.dsenv
          env1.FStarC_TypeChecker_Env.curmodule in
      FStarC_Syntax_Print.term_to_doc' uu___ t1
let (term_to_string :
  FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.term -> Prims.string) =
  fun env1 ->
    fun t ->
      FStarC_GenSym.with_frozen_gensym
        (fun uu___ ->
           let t1 =
             try
               (fun uu___1 ->
                  match () with
                  | () ->
                      normalize
                        [FStarC_TypeChecker_Env.AllowUnboundUniverses] env1 t)
                 ()
             with
             | uu___1 ->
                 (warn_norm_failure t.FStarC_Syntax_Syntax.pos uu___1; t) in
           let uu___1 =
             FStarC_Syntax_DsEnv.set_current_module
               env1.FStarC_TypeChecker_Env.dsenv
               env1.FStarC_TypeChecker_Env.curmodule in
           FStarC_Syntax_Print.term_to_string' uu___1 t1)
let (comp_to_string :
  FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.comp -> Prims.string) =
  fun env1 ->
    fun c ->
      FStarC_GenSym.with_frozen_gensym
        (fun uu___ ->
           let c1 =
             try
               (fun uu___1 ->
                  match () with
                  | () ->
                      let uu___2 =
                        FStarC_TypeChecker_Cfg.config
                          [FStarC_TypeChecker_Env.AllowUnboundUniverses] env1 in
                      norm_comp uu___2 [] c) ()
             with
             | uu___1 ->
                 (warn_norm_failure c.FStarC_Syntax_Syntax.pos uu___1; c) in
           let uu___1 =
             FStarC_Syntax_DsEnv.set_current_module
               env1.FStarC_TypeChecker_Env.dsenv
               env1.FStarC_TypeChecker_Env.curmodule in
           FStarC_Syntax_Print.comp_to_string' uu___1 c1)
let (comp_to_doc :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.comp -> FStarC_Pprint.document)
  =
  fun env1 ->
    fun c ->
      FStarC_GenSym.with_frozen_gensym
        (fun uu___ ->
           let c1 =
             try
               (fun uu___1 ->
                  match () with
                  | () ->
                      let uu___2 =
                        FStarC_TypeChecker_Cfg.config
                          [FStarC_TypeChecker_Env.AllowUnboundUniverses] env1 in
                      norm_comp uu___2 [] c) ()
             with
             | uu___1 ->
                 (warn_norm_failure c.FStarC_Syntax_Syntax.pos uu___1; c) in
           let uu___1 =
             FStarC_Syntax_DsEnv.set_current_module
               env1.FStarC_TypeChecker_Env.dsenv
               env1.FStarC_TypeChecker_Env.curmodule in
           FStarC_Syntax_Print.comp_to_doc' uu___1 c1)
let (normalize_refinement :
  FStarC_TypeChecker_Env.steps ->
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.typ)
  =
  fun steps ->
    fun env1 ->
      fun t0 ->
        let t =
          normalize
            (FStarC_Compiler_List.op_At steps [FStarC_TypeChecker_Env.Beta])
            env1 t0 in
        FStarC_Syntax_Util.flatten_refinement t
let (whnf_steps : FStarC_TypeChecker_Env.step Prims.list) =
  [FStarC_TypeChecker_Env.Primops;
  FStarC_TypeChecker_Env.Weak;
  FStarC_TypeChecker_Env.HNF;
  FStarC_TypeChecker_Env.UnfoldUntil FStarC_Syntax_Syntax.delta_constant;
  FStarC_TypeChecker_Env.Beta]
let (unfold_whnf' :
  FStarC_TypeChecker_Env.steps ->
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun steps ->
    fun env1 ->
      fun t -> normalize (FStarC_Compiler_List.op_At steps whnf_steps) env1 t
let (unfold_whnf :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  = fun env1 -> fun t -> unfold_whnf' [] env1 t
let (reduce_or_remove_uvar_solutions :
  Prims.bool ->
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun remove ->
    fun env1 ->
      fun t ->
        normalize
          (FStarC_Compiler_List.op_At
             (if remove
              then
                [FStarC_TypeChecker_Env.DefaultUnivsToZero;
                FStarC_TypeChecker_Env.CheckNoUvars]
              else [])
             [FStarC_TypeChecker_Env.Beta;
             FStarC_TypeChecker_Env.DoNotUnfoldPureLets;
             FStarC_TypeChecker_Env.CompressUvars;
             FStarC_TypeChecker_Env.Exclude FStarC_TypeChecker_Env.Zeta;
             FStarC_TypeChecker_Env.Exclude FStarC_TypeChecker_Env.Iota;
             FStarC_TypeChecker_Env.NoFullNorm]) env1 t
let (reduce_uvar_solutions :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  = fun env1 -> fun t -> reduce_or_remove_uvar_solutions false env1 t
let (remove_uvar_solutions :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  = fun env1 -> fun t -> reduce_or_remove_uvar_solutions true env1 t
let (eta_expand_with_type :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.term)
  =
  fun env1 ->
    fun e ->
      fun t_e ->
        let uu___ = FStarC_Syntax_Util.arrow_formals_comp t_e in
        match uu___ with
        | (formals, c) ->
            (match formals with
             | [] -> e
             | uu___1 ->
                 let uu___2 = FStarC_Syntax_Util.abs_formals e in
                 (match uu___2 with
                  | (actuals, uu___3, uu___4) ->
                      if
                        (FStarC_Compiler_List.length actuals) =
                          (FStarC_Compiler_List.length formals)
                      then e
                      else
                        (let uu___6 =
                           FStarC_Syntax_Util.args_of_binders formals in
                         match uu___6 with
                         | (binders, args) ->
                             let uu___7 =
                               FStarC_Syntax_Syntax.mk_Tm_app e args
                                 e.FStarC_Syntax_Syntax.pos in
                             let uu___8 =
                               let uu___9 =
                                 FStarC_Syntax_Util.residual_comp_of_comp c in
                               FStar_Pervasives_Native.Some uu___9 in
                             FStarC_Syntax_Util.abs binders uu___7 uu___8)))
let (eta_expand :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun env1 ->
    fun t ->
      match t.FStarC_Syntax_Syntax.n with
      | FStarC_Syntax_Syntax.Tm_name x ->
          eta_expand_with_type env1 t x.FStarC_Syntax_Syntax.sort
      | uu___ ->
          let uu___1 = FStarC_Syntax_Util.head_and_args t in
          (match uu___1 with
           | (head, args) ->
               let uu___2 =
                 let uu___3 = FStarC_Syntax_Subst.compress head in
                 uu___3.FStarC_Syntax_Syntax.n in
               (match uu___2 with
                | FStarC_Syntax_Syntax.Tm_uvar (u, s) ->
                    let uu___3 =
                      let uu___4 =
                        let uu___5 = FStarC_Syntax_Util.ctx_uvar_typ u in
                        FStarC_Syntax_Subst.subst' s uu___5 in
                      FStarC_Syntax_Util.arrow_formals uu___4 in
                    (match uu___3 with
                     | (formals, _tres) ->
                         if
                           (FStarC_Compiler_List.length formals) =
                             (FStarC_Compiler_List.length args)
                         then t
                         else
                           (let uu___5 =
                              env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                {
                                  FStarC_TypeChecker_Env.solver =
                                    (env1.FStarC_TypeChecker_Env.solver);
                                  FStarC_TypeChecker_Env.range =
                                    (env1.FStarC_TypeChecker_Env.range);
                                  FStarC_TypeChecker_Env.curmodule =
                                    (env1.FStarC_TypeChecker_Env.curmodule);
                                  FStarC_TypeChecker_Env.gamma =
                                    (env1.FStarC_TypeChecker_Env.gamma);
                                  FStarC_TypeChecker_Env.gamma_sig =
                                    (env1.FStarC_TypeChecker_Env.gamma_sig);
                                  FStarC_TypeChecker_Env.gamma_cache =
                                    (env1.FStarC_TypeChecker_Env.gamma_cache);
                                  FStarC_TypeChecker_Env.modules =
                                    (env1.FStarC_TypeChecker_Env.modules);
                                  FStarC_TypeChecker_Env.expected_typ =
                                    FStar_Pervasives_Native.None;
                                  FStarC_TypeChecker_Env.sigtab =
                                    (env1.FStarC_TypeChecker_Env.sigtab);
                                  FStarC_TypeChecker_Env.attrtab =
                                    (env1.FStarC_TypeChecker_Env.attrtab);
                                  FStarC_TypeChecker_Env.instantiate_imp =
                                    (env1.FStarC_TypeChecker_Env.instantiate_imp);
                                  FStarC_TypeChecker_Env.effects =
                                    (env1.FStarC_TypeChecker_Env.effects);
                                  FStarC_TypeChecker_Env.generalize =
                                    (env1.FStarC_TypeChecker_Env.generalize);
                                  FStarC_TypeChecker_Env.letrecs =
                                    (env1.FStarC_TypeChecker_Env.letrecs);
                                  FStarC_TypeChecker_Env.top_level =
                                    (env1.FStarC_TypeChecker_Env.top_level);
                                  FStarC_TypeChecker_Env.check_uvars =
                                    (env1.FStarC_TypeChecker_Env.check_uvars);
                                  FStarC_TypeChecker_Env.use_eq_strict =
                                    (env1.FStarC_TypeChecker_Env.use_eq_strict);
                                  FStarC_TypeChecker_Env.is_iface =
                                    (env1.FStarC_TypeChecker_Env.is_iface);
                                  FStarC_TypeChecker_Env.admit = true;
                                  FStarC_TypeChecker_Env.lax_universes =
                                    (env1.FStarC_TypeChecker_Env.lax_universes);
                                  FStarC_TypeChecker_Env.phase1 =
                                    (env1.FStarC_TypeChecker_Env.phase1);
                                  FStarC_TypeChecker_Env.failhard =
                                    (env1.FStarC_TypeChecker_Env.failhard);
                                  FStarC_TypeChecker_Env.flychecking =
                                    (env1.FStarC_TypeChecker_Env.flychecking);
                                  FStarC_TypeChecker_Env.uvar_subtyping =
                                    (env1.FStarC_TypeChecker_Env.uvar_subtyping);
                                  FStarC_TypeChecker_Env.intactics =
                                    (env1.FStarC_TypeChecker_Env.intactics);
                                  FStarC_TypeChecker_Env.nocoerce =
                                    (env1.FStarC_TypeChecker_Env.nocoerce);
                                  FStarC_TypeChecker_Env.tc_term =
                                    (env1.FStarC_TypeChecker_Env.tc_term);
                                  FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                    =
                                    (env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                  FStarC_TypeChecker_Env.universe_of =
                                    (env1.FStarC_TypeChecker_Env.universe_of);
                                  FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                    =
                                    (env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                  FStarC_TypeChecker_Env.teq_nosmt_force =
                                    (env1.FStarC_TypeChecker_Env.teq_nosmt_force);
                                  FStarC_TypeChecker_Env.subtype_nosmt_force
                                    =
                                    (env1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                  FStarC_TypeChecker_Env.qtbl_name_and_index
                                    =
                                    (env1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                  FStarC_TypeChecker_Env.normalized_eff_names
                                    =
                                    (env1.FStarC_TypeChecker_Env.normalized_eff_names);
                                  FStarC_TypeChecker_Env.fv_delta_depths =
                                    (env1.FStarC_TypeChecker_Env.fv_delta_depths);
                                  FStarC_TypeChecker_Env.proof_ns =
                                    (env1.FStarC_TypeChecker_Env.proof_ns);
                                  FStarC_TypeChecker_Env.synth_hook =
                                    (env1.FStarC_TypeChecker_Env.synth_hook);
                                  FStarC_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (env1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                  FStarC_TypeChecker_Env.splice =
                                    (env1.FStarC_TypeChecker_Env.splice);
                                  FStarC_TypeChecker_Env.mpreprocess =
                                    (env1.FStarC_TypeChecker_Env.mpreprocess);
                                  FStarC_TypeChecker_Env.postprocess =
                                    (env1.FStarC_TypeChecker_Env.postprocess);
                                  FStarC_TypeChecker_Env.identifier_info =
                                    (env1.FStarC_TypeChecker_Env.identifier_info);
                                  FStarC_TypeChecker_Env.tc_hooks =
                                    (env1.FStarC_TypeChecker_Env.tc_hooks);
                                  FStarC_TypeChecker_Env.dsenv =
                                    (env1.FStarC_TypeChecker_Env.dsenv);
                                  FStarC_TypeChecker_Env.nbe =
                                    (env1.FStarC_TypeChecker_Env.nbe);
                                  FStarC_TypeChecker_Env.strict_args_tab =
                                    (env1.FStarC_TypeChecker_Env.strict_args_tab);
                                  FStarC_TypeChecker_Env.erasable_types_tab =
                                    (env1.FStarC_TypeChecker_Env.erasable_types_tab);
                                  FStarC_TypeChecker_Env.enable_defer_to_tac
                                    =
                                    (env1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                  FStarC_TypeChecker_Env.unif_allow_ref_guards
                                    =
                                    (env1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                  FStarC_TypeChecker_Env.erase_erasable_args
                                    =
                                    (env1.FStarC_TypeChecker_Env.erase_erasable_args);
                                  FStarC_TypeChecker_Env.core_check =
                                    (env1.FStarC_TypeChecker_Env.core_check);
                                  FStarC_TypeChecker_Env.missing_decl =
                                    (env1.FStarC_TypeChecker_Env.missing_decl)
                                } t true in
                            match uu___5 with
                            | (uu___6, ty, uu___7) ->
                                eta_expand_with_type env1 t ty))
                | uu___3 ->
                    let uu___4 =
                      env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                        {
                          FStarC_TypeChecker_Env.solver =
                            (env1.FStarC_TypeChecker_Env.solver);
                          FStarC_TypeChecker_Env.range =
                            (env1.FStarC_TypeChecker_Env.range);
                          FStarC_TypeChecker_Env.curmodule =
                            (env1.FStarC_TypeChecker_Env.curmodule);
                          FStarC_TypeChecker_Env.gamma =
                            (env1.FStarC_TypeChecker_Env.gamma);
                          FStarC_TypeChecker_Env.gamma_sig =
                            (env1.FStarC_TypeChecker_Env.gamma_sig);
                          FStarC_TypeChecker_Env.gamma_cache =
                            (env1.FStarC_TypeChecker_Env.gamma_cache);
                          FStarC_TypeChecker_Env.modules =
                            (env1.FStarC_TypeChecker_Env.modules);
                          FStarC_TypeChecker_Env.expected_typ =
                            FStar_Pervasives_Native.None;
                          FStarC_TypeChecker_Env.sigtab =
                            (env1.FStarC_TypeChecker_Env.sigtab);
                          FStarC_TypeChecker_Env.attrtab =
                            (env1.FStarC_TypeChecker_Env.attrtab);
                          FStarC_TypeChecker_Env.instantiate_imp =
                            (env1.FStarC_TypeChecker_Env.instantiate_imp);
                          FStarC_TypeChecker_Env.effects =
                            (env1.FStarC_TypeChecker_Env.effects);
                          FStarC_TypeChecker_Env.generalize =
                            (env1.FStarC_TypeChecker_Env.generalize);
                          FStarC_TypeChecker_Env.letrecs =
                            (env1.FStarC_TypeChecker_Env.letrecs);
                          FStarC_TypeChecker_Env.top_level =
                            (env1.FStarC_TypeChecker_Env.top_level);
                          FStarC_TypeChecker_Env.check_uvars =
                            (env1.FStarC_TypeChecker_Env.check_uvars);
                          FStarC_TypeChecker_Env.use_eq_strict =
                            (env1.FStarC_TypeChecker_Env.use_eq_strict);
                          FStarC_TypeChecker_Env.is_iface =
                            (env1.FStarC_TypeChecker_Env.is_iface);
                          FStarC_TypeChecker_Env.admit = true;
                          FStarC_TypeChecker_Env.lax_universes =
                            (env1.FStarC_TypeChecker_Env.lax_universes);
                          FStarC_TypeChecker_Env.phase1 =
                            (env1.FStarC_TypeChecker_Env.phase1);
                          FStarC_TypeChecker_Env.failhard =
                            (env1.FStarC_TypeChecker_Env.failhard);
                          FStarC_TypeChecker_Env.flychecking =
                            (env1.FStarC_TypeChecker_Env.flychecking);
                          FStarC_TypeChecker_Env.uvar_subtyping =
                            (env1.FStarC_TypeChecker_Env.uvar_subtyping);
                          FStarC_TypeChecker_Env.intactics =
                            (env1.FStarC_TypeChecker_Env.intactics);
                          FStarC_TypeChecker_Env.nocoerce =
                            (env1.FStarC_TypeChecker_Env.nocoerce);
                          FStarC_TypeChecker_Env.tc_term =
                            (env1.FStarC_TypeChecker_Env.tc_term);
                          FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                            (env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                          FStarC_TypeChecker_Env.universe_of =
                            (env1.FStarC_TypeChecker_Env.universe_of);
                          FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                            =
                            (env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                          FStarC_TypeChecker_Env.teq_nosmt_force =
                            (env1.FStarC_TypeChecker_Env.teq_nosmt_force);
                          FStarC_TypeChecker_Env.subtype_nosmt_force =
                            (env1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                          FStarC_TypeChecker_Env.qtbl_name_and_index =
                            (env1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                          FStarC_TypeChecker_Env.normalized_eff_names =
                            (env1.FStarC_TypeChecker_Env.normalized_eff_names);
                          FStarC_TypeChecker_Env.fv_delta_depths =
                            (env1.FStarC_TypeChecker_Env.fv_delta_depths);
                          FStarC_TypeChecker_Env.proof_ns =
                            (env1.FStarC_TypeChecker_Env.proof_ns);
                          FStarC_TypeChecker_Env.synth_hook =
                            (env1.FStarC_TypeChecker_Env.synth_hook);
                          FStarC_TypeChecker_Env.try_solve_implicits_hook =
                            (env1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                          FStarC_TypeChecker_Env.splice =
                            (env1.FStarC_TypeChecker_Env.splice);
                          FStarC_TypeChecker_Env.mpreprocess =
                            (env1.FStarC_TypeChecker_Env.mpreprocess);
                          FStarC_TypeChecker_Env.postprocess =
                            (env1.FStarC_TypeChecker_Env.postprocess);
                          FStarC_TypeChecker_Env.identifier_info =
                            (env1.FStarC_TypeChecker_Env.identifier_info);
                          FStarC_TypeChecker_Env.tc_hooks =
                            (env1.FStarC_TypeChecker_Env.tc_hooks);
                          FStarC_TypeChecker_Env.dsenv =
                            (env1.FStarC_TypeChecker_Env.dsenv);
                          FStarC_TypeChecker_Env.nbe =
                            (env1.FStarC_TypeChecker_Env.nbe);
                          FStarC_TypeChecker_Env.strict_args_tab =
                            (env1.FStarC_TypeChecker_Env.strict_args_tab);
                          FStarC_TypeChecker_Env.erasable_types_tab =
                            (env1.FStarC_TypeChecker_Env.erasable_types_tab);
                          FStarC_TypeChecker_Env.enable_defer_to_tac =
                            (env1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                          FStarC_TypeChecker_Env.unif_allow_ref_guards =
                            (env1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                          FStarC_TypeChecker_Env.erase_erasable_args =
                            (env1.FStarC_TypeChecker_Env.erase_erasable_args);
                          FStarC_TypeChecker_Env.core_check =
                            (env1.FStarC_TypeChecker_Env.core_check);
                          FStarC_TypeChecker_Env.missing_decl =
                            (env1.FStarC_TypeChecker_Env.missing_decl)
                        } t true in
                    (match uu___4 with
                     | (uu___5, ty, uu___6) -> eta_expand_with_type env1 t ty)))
let (elim_uvars_aux_tc :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.univ_names ->
      FStarC_Syntax_Syntax.binders ->
        (FStarC_Syntax_Syntax.typ, FStarC_Syntax_Syntax.comp)
          FStar_Pervasives.either ->
          (FStarC_Syntax_Syntax.univ_names * FStarC_Syntax_Syntax.binder
            Prims.list *
            (FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax,
            FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax)
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
                FStarC_Syntax_Syntax.mk
                  (FStarC_Syntax_Syntax.Tm_arrow
                     {
                       FStarC_Syntax_Syntax.bs1 = binders;
                       FStarC_Syntax_Syntax.comp = c
                     }) c.FStarC_Syntax_Syntax.pos
            | (uu___, FStar_Pervasives.Inl t1) ->
                let uu___1 =
                  let uu___2 =
                    let uu___3 = FStarC_Syntax_Syntax.mk_Total t1 in
                    {
                      FStarC_Syntax_Syntax.bs1 = binders;
                      FStarC_Syntax_Syntax.comp = uu___3
                    } in
                  FStarC_Syntax_Syntax.Tm_arrow uu___2 in
                FStarC_Syntax_Syntax.mk uu___1 t1.FStarC_Syntax_Syntax.pos in
          let uu___ = FStarC_Syntax_Subst.open_univ_vars univ_names t in
          match uu___ with
          | (univ_names1, t1) ->
              let t2 = remove_uvar_solutions env1 t1 in
              let t3 = FStarC_Syntax_Subst.close_univ_vars univ_names1 t2 in
              let uu___1 =
                match binders with
                | [] -> ([], (FStar_Pervasives.Inl t3))
                | uu___2 ->
                    let uu___3 =
                      let uu___4 =
                        let uu___5 = FStarC_Syntax_Subst.compress t3 in
                        uu___5.FStarC_Syntax_Syntax.n in
                      (uu___4, tc) in
                    (match uu___3 with
                     | (FStarC_Syntax_Syntax.Tm_arrow
                        { FStarC_Syntax_Syntax.bs1 = binders1;
                          FStarC_Syntax_Syntax.comp = c;_},
                        FStar_Pervasives.Inr uu___4) ->
                         (binders1, (FStar_Pervasives.Inr c))
                     | (FStarC_Syntax_Syntax.Tm_arrow
                        { FStarC_Syntax_Syntax.bs1 = binders1;
                          FStarC_Syntax_Syntax.comp = c;_},
                        FStar_Pervasives.Inl uu___4) ->
                         (binders1,
                           (FStar_Pervasives.Inl
                              (FStarC_Syntax_Util.comp_result c)))
                     | (uu___4, FStar_Pervasives.Inl uu___5) ->
                         ([], (FStar_Pervasives.Inl t3))
                     | uu___4 -> failwith "Impossible") in
              (match uu___1 with
               | (binders1, tc1) -> (univ_names1, binders1, tc1))
let (elim_uvars_aux_t :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.univ_names ->
      FStarC_Syntax_Syntax.binders ->
        FStarC_Syntax_Syntax.typ ->
          (FStarC_Syntax_Syntax.univ_names * FStarC_Syntax_Syntax.binder
            Prims.list * FStarC_Syntax_Syntax.term'
            FStarC_Syntax_Syntax.syntax))
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
              let uu___1 = FStarC_Compiler_Util.left tc in
              (univ_names1, binders1, uu___1)
let (elim_uvars_aux_c :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.univ_names ->
      FStarC_Syntax_Syntax.binders ->
        FStarC_Syntax_Syntax.comp ->
          (FStarC_Syntax_Syntax.univ_names * FStarC_Syntax_Syntax.binder
            Prims.list * FStarC_Syntax_Syntax.comp'
            FStarC_Syntax_Syntax.syntax))
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
              let uu___1 = FStarC_Compiler_Util.right tc in
              (univ_names1, binders1, uu___1)
let rec (elim_uvars :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.sigelt -> FStarC_Syntax_Syntax.sigelt)
  =
  fun env1 ->
    fun s ->
      let sigattrs =
        let uu___ =
          FStarC_Compiler_List.map (elim_uvars_aux_t env1 [] [])
            s.FStarC_Syntax_Syntax.sigattrs in
        FStarC_Compiler_List.map
          FStar_Pervasives_Native.__proj__Mktuple3__item___3 uu___ in
      let s1 =
        {
          FStarC_Syntax_Syntax.sigel = (s.FStarC_Syntax_Syntax.sigel);
          FStarC_Syntax_Syntax.sigrng = (s.FStarC_Syntax_Syntax.sigrng);
          FStarC_Syntax_Syntax.sigquals = (s.FStarC_Syntax_Syntax.sigquals);
          FStarC_Syntax_Syntax.sigmeta = (s.FStarC_Syntax_Syntax.sigmeta);
          FStarC_Syntax_Syntax.sigattrs = sigattrs;
          FStarC_Syntax_Syntax.sigopens_and_abbrevs =
            (s.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
          FStarC_Syntax_Syntax.sigopts = (s.FStarC_Syntax_Syntax.sigopts)
        } in
      match s1.FStarC_Syntax_Syntax.sigel with
      | FStarC_Syntax_Syntax.Sig_inductive_typ
          { FStarC_Syntax_Syntax.lid = lid;
            FStarC_Syntax_Syntax.us = univ_names;
            FStarC_Syntax_Syntax.params = binders;
            FStarC_Syntax_Syntax.num_uniform_params = num_uniform;
            FStarC_Syntax_Syntax.t = typ;
            FStarC_Syntax_Syntax.mutuals = lids;
            FStarC_Syntax_Syntax.ds = lids';
            FStarC_Syntax_Syntax.injective_type_params =
              injective_type_params;_}
          ->
          let uu___ = elim_uvars_aux_t env1 univ_names binders typ in
          (match uu___ with
           | (univ_names1, binders1, typ1) ->
               {
                 FStarC_Syntax_Syntax.sigel =
                   (FStarC_Syntax_Syntax.Sig_inductive_typ
                      {
                        FStarC_Syntax_Syntax.lid = lid;
                        FStarC_Syntax_Syntax.us = univ_names1;
                        FStarC_Syntax_Syntax.params = binders1;
                        FStarC_Syntax_Syntax.num_uniform_params = num_uniform;
                        FStarC_Syntax_Syntax.t = typ1;
                        FStarC_Syntax_Syntax.mutuals = lids;
                        FStarC_Syntax_Syntax.ds = lids';
                        FStarC_Syntax_Syntax.injective_type_params =
                          injective_type_params
                      });
                 FStarC_Syntax_Syntax.sigrng =
                   (s1.FStarC_Syntax_Syntax.sigrng);
                 FStarC_Syntax_Syntax.sigquals =
                   (s1.FStarC_Syntax_Syntax.sigquals);
                 FStarC_Syntax_Syntax.sigmeta =
                   (s1.FStarC_Syntax_Syntax.sigmeta);
                 FStarC_Syntax_Syntax.sigattrs =
                   (s1.FStarC_Syntax_Syntax.sigattrs);
                 FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                   (s1.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                 FStarC_Syntax_Syntax.sigopts =
                   (s1.FStarC_Syntax_Syntax.sigopts)
               })
      | FStarC_Syntax_Syntax.Sig_bundle
          { FStarC_Syntax_Syntax.ses = sigs;
            FStarC_Syntax_Syntax.lids = lids;_}
          ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_Compiler_List.map (elim_uvars env1) sigs in
              {
                FStarC_Syntax_Syntax.ses = uu___2;
                FStarC_Syntax_Syntax.lids = lids
              } in
            FStarC_Syntax_Syntax.Sig_bundle uu___1 in
          {
            FStarC_Syntax_Syntax.sigel = uu___;
            FStarC_Syntax_Syntax.sigrng = (s1.FStarC_Syntax_Syntax.sigrng);
            FStarC_Syntax_Syntax.sigquals =
              (s1.FStarC_Syntax_Syntax.sigquals);
            FStarC_Syntax_Syntax.sigmeta = (s1.FStarC_Syntax_Syntax.sigmeta);
            FStarC_Syntax_Syntax.sigattrs =
              (s1.FStarC_Syntax_Syntax.sigattrs);
            FStarC_Syntax_Syntax.sigopens_and_abbrevs =
              (s1.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
            FStarC_Syntax_Syntax.sigopts = (s1.FStarC_Syntax_Syntax.sigopts)
          }
      | FStarC_Syntax_Syntax.Sig_datacon
          { FStarC_Syntax_Syntax.lid1 = lid;
            FStarC_Syntax_Syntax.us1 = univ_names;
            FStarC_Syntax_Syntax.t1 = typ;
            FStarC_Syntax_Syntax.ty_lid = lident;
            FStarC_Syntax_Syntax.num_ty_params = i;
            FStarC_Syntax_Syntax.mutuals1 = lids;
            FStarC_Syntax_Syntax.injective_type_params1 =
              injective_type_params;_}
          ->
          let uu___ = elim_uvars_aux_t env1 univ_names [] typ in
          (match uu___ with
           | (univ_names1, uu___1, typ1) ->
               {
                 FStarC_Syntax_Syntax.sigel =
                   (FStarC_Syntax_Syntax.Sig_datacon
                      {
                        FStarC_Syntax_Syntax.lid1 = lid;
                        FStarC_Syntax_Syntax.us1 = univ_names1;
                        FStarC_Syntax_Syntax.t1 = typ1;
                        FStarC_Syntax_Syntax.ty_lid = lident;
                        FStarC_Syntax_Syntax.num_ty_params = i;
                        FStarC_Syntax_Syntax.mutuals1 = lids;
                        FStarC_Syntax_Syntax.injective_type_params1 =
                          injective_type_params
                      });
                 FStarC_Syntax_Syntax.sigrng =
                   (s1.FStarC_Syntax_Syntax.sigrng);
                 FStarC_Syntax_Syntax.sigquals =
                   (s1.FStarC_Syntax_Syntax.sigquals);
                 FStarC_Syntax_Syntax.sigmeta =
                   (s1.FStarC_Syntax_Syntax.sigmeta);
                 FStarC_Syntax_Syntax.sigattrs =
                   (s1.FStarC_Syntax_Syntax.sigattrs);
                 FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                   (s1.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                 FStarC_Syntax_Syntax.sigopts =
                   (s1.FStarC_Syntax_Syntax.sigopts)
               })
      | FStarC_Syntax_Syntax.Sig_declare_typ
          { FStarC_Syntax_Syntax.lid2 = lid;
            FStarC_Syntax_Syntax.us2 = univ_names;
            FStarC_Syntax_Syntax.t2 = typ;_}
          ->
          let uu___ = elim_uvars_aux_t env1 univ_names [] typ in
          (match uu___ with
           | (univ_names1, uu___1, typ1) ->
               {
                 FStarC_Syntax_Syntax.sigel =
                   (FStarC_Syntax_Syntax.Sig_declare_typ
                      {
                        FStarC_Syntax_Syntax.lid2 = lid;
                        FStarC_Syntax_Syntax.us2 = univ_names1;
                        FStarC_Syntax_Syntax.t2 = typ1
                      });
                 FStarC_Syntax_Syntax.sigrng =
                   (s1.FStarC_Syntax_Syntax.sigrng);
                 FStarC_Syntax_Syntax.sigquals =
                   (s1.FStarC_Syntax_Syntax.sigquals);
                 FStarC_Syntax_Syntax.sigmeta =
                   (s1.FStarC_Syntax_Syntax.sigmeta);
                 FStarC_Syntax_Syntax.sigattrs =
                   (s1.FStarC_Syntax_Syntax.sigattrs);
                 FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                   (s1.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                 FStarC_Syntax_Syntax.sigopts =
                   (s1.FStarC_Syntax_Syntax.sigopts)
               })
      | FStarC_Syntax_Syntax.Sig_let
          { FStarC_Syntax_Syntax.lbs1 = (b, lbs);
            FStarC_Syntax_Syntax.lids1 = lids;_}
          ->
          let lbs1 =
            FStarC_Compiler_List.map
              (fun lb ->
                 let uu___ =
                   FStarC_Syntax_Subst.univ_var_opening
                     lb.FStarC_Syntax_Syntax.lbunivs in
                 match uu___ with
                 | (opening, lbunivs) ->
                     let elim t =
                       let uu___1 =
                         let uu___2 = FStarC_Syntax_Subst.subst opening t in
                         remove_uvar_solutions env1 uu___2 in
                       FStarC_Syntax_Subst.close_univ_vars lbunivs uu___1 in
                     let lbtyp = elim lb.FStarC_Syntax_Syntax.lbtyp in
                     let lbdef = elim lb.FStarC_Syntax_Syntax.lbdef in
                     {
                       FStarC_Syntax_Syntax.lbname =
                         (lb.FStarC_Syntax_Syntax.lbname);
                       FStarC_Syntax_Syntax.lbunivs = lbunivs;
                       FStarC_Syntax_Syntax.lbtyp = lbtyp;
                       FStarC_Syntax_Syntax.lbeff =
                         (lb.FStarC_Syntax_Syntax.lbeff);
                       FStarC_Syntax_Syntax.lbdef = lbdef;
                       FStarC_Syntax_Syntax.lbattrs =
                         (lb.FStarC_Syntax_Syntax.lbattrs);
                       FStarC_Syntax_Syntax.lbpos =
                         (lb.FStarC_Syntax_Syntax.lbpos)
                     }) lbs in
          {
            FStarC_Syntax_Syntax.sigel =
              (FStarC_Syntax_Syntax.Sig_let
                 {
                   FStarC_Syntax_Syntax.lbs1 = (b, lbs1);
                   FStarC_Syntax_Syntax.lids1 = lids
                 });
            FStarC_Syntax_Syntax.sigrng = (s1.FStarC_Syntax_Syntax.sigrng);
            FStarC_Syntax_Syntax.sigquals =
              (s1.FStarC_Syntax_Syntax.sigquals);
            FStarC_Syntax_Syntax.sigmeta = (s1.FStarC_Syntax_Syntax.sigmeta);
            FStarC_Syntax_Syntax.sigattrs =
              (s1.FStarC_Syntax_Syntax.sigattrs);
            FStarC_Syntax_Syntax.sigopens_and_abbrevs =
              (s1.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
            FStarC_Syntax_Syntax.sigopts = (s1.FStarC_Syntax_Syntax.sigopts)
          }
      | FStarC_Syntax_Syntax.Sig_assume
          { FStarC_Syntax_Syntax.lid3 = l; FStarC_Syntax_Syntax.us3 = us;
            FStarC_Syntax_Syntax.phi1 = t;_}
          ->
          let uu___ = elim_uvars_aux_t env1 us [] t in
          (match uu___ with
           | (us1, uu___1, t1) ->
               {
                 FStarC_Syntax_Syntax.sigel =
                   (FStarC_Syntax_Syntax.Sig_assume
                      {
                        FStarC_Syntax_Syntax.lid3 = l;
                        FStarC_Syntax_Syntax.us3 = us1;
                        FStarC_Syntax_Syntax.phi1 = t1
                      });
                 FStarC_Syntax_Syntax.sigrng =
                   (s1.FStarC_Syntax_Syntax.sigrng);
                 FStarC_Syntax_Syntax.sigquals =
                   (s1.FStarC_Syntax_Syntax.sigquals);
                 FStarC_Syntax_Syntax.sigmeta =
                   (s1.FStarC_Syntax_Syntax.sigmeta);
                 FStarC_Syntax_Syntax.sigattrs =
                   (s1.FStarC_Syntax_Syntax.sigattrs);
                 FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                   (s1.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                 FStarC_Syntax_Syntax.sigopts =
                   (s1.FStarC_Syntax_Syntax.sigopts)
               })
      | FStarC_Syntax_Syntax.Sig_new_effect ed ->
          let uu___ =
            elim_uvars_aux_t env1 ed.FStarC_Syntax_Syntax.univs
              ed.FStarC_Syntax_Syntax.binders FStarC_Syntax_Syntax.t_unit in
          (match uu___ with
           | (univs, binders, uu___1) ->
               let uu___2 =
                 let uu___3 = FStarC_Syntax_Subst.univ_var_opening univs in
                 match uu___3 with
                 | (univs_opening, univs1) ->
                     let uu___4 = FStarC_Syntax_Subst.univ_var_closing univs1 in
                     (univs_opening, uu___4) in
               (match uu___2 with
                | (univs_opening, univs_closing) ->
                    let uu___3 =
                      let binders1 = FStarC_Syntax_Subst.open_binders binders in
                      let uu___4 =
                        FStarC_Syntax_Subst.opening_of_binders binders1 in
                      let uu___5 =
                        FStarC_Syntax_Subst.closing_of_binders binders1 in
                      (uu___4, uu___5) in
                    (match uu___3 with
                     | (b_opening, b_closing) ->
                         let n = FStarC_Compiler_List.length univs in
                         let n_binders = FStarC_Compiler_List.length binders in
                         let elim_tscheme uu___4 =
                           match uu___4 with
                           | (us, t) ->
                               let n_us = FStarC_Compiler_List.length us in
                               let uu___5 =
                                 FStarC_Syntax_Subst.open_univ_vars us t in
                               (match uu___5 with
                                | (us1, t1) ->
                                    let uu___6 =
                                      let uu___7 =
                                        FStarC_Syntax_Subst.shift_subst n_us
                                          b_opening in
                                      let uu___8 =
                                        FStarC_Syntax_Subst.shift_subst n_us
                                          b_closing in
                                      (uu___7, uu___8) in
                                    (match uu___6 with
                                     | (b_opening1, b_closing1) ->
                                         let uu___7 =
                                           let uu___8 =
                                             FStarC_Syntax_Subst.shift_subst
                                               (n_us + n_binders)
                                               univs_opening in
                                           let uu___9 =
                                             FStarC_Syntax_Subst.shift_subst
                                               (n_us + n_binders)
                                               univs_closing in
                                           (uu___8, uu___9) in
                                         (match uu___7 with
                                          | (univs_opening1, univs_closing1)
                                              ->
                                              let t2 =
                                                let uu___8 =
                                                  FStarC_Syntax_Subst.subst
                                                    b_opening1 t1 in
                                                FStarC_Syntax_Subst.subst
                                                  univs_opening1 uu___8 in
                                              let uu___8 =
                                                elim_uvars_aux_t env1 [] []
                                                  t2 in
                                              (match uu___8 with
                                               | (uu___9, uu___10, t3) ->
                                                   let t4 =
                                                     let uu___11 =
                                                       let uu___12 =
                                                         FStarC_Syntax_Subst.close_univ_vars
                                                           us1 t3 in
                                                       FStarC_Syntax_Subst.subst
                                                         b_closing1 uu___12 in
                                                     FStarC_Syntax_Subst.subst
                                                       univs_closing1 uu___11 in
                                                   (us1, t4))))) in
                         let elim_term t =
                           let uu___4 = elim_uvars_aux_t env1 univs binders t in
                           match uu___4 with | (uu___5, uu___6, t1) -> t1 in
                         let elim_action a =
                           let action_typ_templ =
                             let body =
                               FStarC_Syntax_Syntax.mk
                                 (FStarC_Syntax_Syntax.Tm_ascribed
                                    {
                                      FStarC_Syntax_Syntax.tm =
                                        (a.FStarC_Syntax_Syntax.action_defn);
                                      FStarC_Syntax_Syntax.asc =
                                        ((FStar_Pervasives.Inl
                                            (a.FStarC_Syntax_Syntax.action_typ)),
                                          FStar_Pervasives_Native.None,
                                          false);
                                      FStarC_Syntax_Syntax.eff_opt =
                                        FStar_Pervasives_Native.None
                                    })
                                 (a.FStarC_Syntax_Syntax.action_defn).FStarC_Syntax_Syntax.pos in
                             match a.FStarC_Syntax_Syntax.action_params with
                             | [] -> body
                             | uu___4 ->
                                 FStarC_Syntax_Syntax.mk
                                   (FStarC_Syntax_Syntax.Tm_abs
                                      {
                                        FStarC_Syntax_Syntax.bs =
                                          (a.FStarC_Syntax_Syntax.action_params);
                                        FStarC_Syntax_Syntax.body = body;
                                        FStarC_Syntax_Syntax.rc_opt =
                                          FStar_Pervasives_Native.None
                                      })
                                   (a.FStarC_Syntax_Syntax.action_defn).FStarC_Syntax_Syntax.pos in
                           let destruct_action_body body =
                             let uu___4 =
                               let uu___5 = FStarC_Syntax_Subst.compress body in
                               uu___5.FStarC_Syntax_Syntax.n in
                             match uu___4 with
                             | FStarC_Syntax_Syntax.Tm_ascribed
                                 { FStarC_Syntax_Syntax.tm = defn;
                                   FStarC_Syntax_Syntax.asc =
                                     (FStar_Pervasives.Inl typ,
                                      FStar_Pervasives_Native.None, uu___5);
                                   FStarC_Syntax_Syntax.eff_opt =
                                     FStar_Pervasives_Native.None;_}
                                 -> (defn, typ)
                             | uu___5 -> failwith "Impossible" in
                           let destruct_action_typ_templ t =
                             let uu___4 =
                               let uu___5 = FStarC_Syntax_Subst.compress t in
                               uu___5.FStarC_Syntax_Syntax.n in
                             match uu___4 with
                             | FStarC_Syntax_Syntax.Tm_abs
                                 { FStarC_Syntax_Syntax.bs = pars;
                                   FStarC_Syntax_Syntax.body = body;
                                   FStarC_Syntax_Syntax.rc_opt = uu___5;_}
                                 ->
                                 let uu___6 = destruct_action_body body in
                                 (match uu___6 with
                                  | (defn, typ) -> (pars, defn, typ))
                             | uu___5 ->
                                 let uu___6 = destruct_action_body t in
                                 (match uu___6 with
                                  | (defn, typ) -> ([], defn, typ)) in
                           let uu___4 =
                             elim_tscheme
                               ((a.FStarC_Syntax_Syntax.action_univs),
                                 action_typ_templ) in
                           match uu___4 with
                           | (action_univs, t) ->
                               let uu___5 = destruct_action_typ_templ t in
                               (match uu___5 with
                                | (action_params, action_defn, action_typ) ->
                                    let a' =
                                      {
                                        FStarC_Syntax_Syntax.action_name =
                                          (a.FStarC_Syntax_Syntax.action_name);
                                        FStarC_Syntax_Syntax.action_unqualified_name
                                          =
                                          (a.FStarC_Syntax_Syntax.action_unqualified_name);
                                        FStarC_Syntax_Syntax.action_univs =
                                          action_univs;
                                        FStarC_Syntax_Syntax.action_params =
                                          action_params;
                                        FStarC_Syntax_Syntax.action_defn =
                                          action_defn;
                                        FStarC_Syntax_Syntax.action_typ =
                                          action_typ
                                      } in
                                    a') in
                         let ed1 =
                           let uu___4 =
                             FStarC_Syntax_Util.apply_eff_sig elim_tscheme
                               ed.FStarC_Syntax_Syntax.signature in
                           let uu___5 =
                             FStarC_Syntax_Util.apply_eff_combinators
                               elim_tscheme
                               ed.FStarC_Syntax_Syntax.combinators in
                           let uu___6 =
                             FStarC_Compiler_List.map elim_action
                               ed.FStarC_Syntax_Syntax.actions in
                           {
                             FStarC_Syntax_Syntax.mname =
                               (ed.FStarC_Syntax_Syntax.mname);
                             FStarC_Syntax_Syntax.cattributes =
                               (ed.FStarC_Syntax_Syntax.cattributes);
                             FStarC_Syntax_Syntax.univs = univs;
                             FStarC_Syntax_Syntax.binders = binders;
                             FStarC_Syntax_Syntax.signature = uu___4;
                             FStarC_Syntax_Syntax.combinators = uu___5;
                             FStarC_Syntax_Syntax.actions = uu___6;
                             FStarC_Syntax_Syntax.eff_attrs =
                               (ed.FStarC_Syntax_Syntax.eff_attrs);
                             FStarC_Syntax_Syntax.extraction_mode =
                               (ed.FStarC_Syntax_Syntax.extraction_mode)
                           } in
                         {
                           FStarC_Syntax_Syntax.sigel =
                             (FStarC_Syntax_Syntax.Sig_new_effect ed1);
                           FStarC_Syntax_Syntax.sigrng =
                             (s1.FStarC_Syntax_Syntax.sigrng);
                           FStarC_Syntax_Syntax.sigquals =
                             (s1.FStarC_Syntax_Syntax.sigquals);
                           FStarC_Syntax_Syntax.sigmeta =
                             (s1.FStarC_Syntax_Syntax.sigmeta);
                           FStarC_Syntax_Syntax.sigattrs =
                             (s1.FStarC_Syntax_Syntax.sigattrs);
                           FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                             (s1.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                           FStarC_Syntax_Syntax.sigopts =
                             (s1.FStarC_Syntax_Syntax.sigopts)
                         })))
      | FStarC_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___ =
            match uu___ with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us, t) ->
                let uu___1 = elim_uvars_aux_t env1 us [] t in
                (match uu___1 with
                 | (us1, uu___2, t1) ->
                     FStar_Pervasives_Native.Some (us1, t1)) in
          let sub_eff1 =
            let uu___ = elim_tscheme_opt sub_eff.FStarC_Syntax_Syntax.lift_wp in
            let uu___1 = elim_tscheme_opt sub_eff.FStarC_Syntax_Syntax.lift in
            {
              FStarC_Syntax_Syntax.source =
                (sub_eff.FStarC_Syntax_Syntax.source);
              FStarC_Syntax_Syntax.target =
                (sub_eff.FStarC_Syntax_Syntax.target);
              FStarC_Syntax_Syntax.lift_wp = uu___;
              FStarC_Syntax_Syntax.lift = uu___1;
              FStarC_Syntax_Syntax.kind = (sub_eff.FStarC_Syntax_Syntax.kind)
            } in
          {
            FStarC_Syntax_Syntax.sigel =
              (FStarC_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStarC_Syntax_Syntax.sigrng = (s1.FStarC_Syntax_Syntax.sigrng);
            FStarC_Syntax_Syntax.sigquals =
              (s1.FStarC_Syntax_Syntax.sigquals);
            FStarC_Syntax_Syntax.sigmeta = (s1.FStarC_Syntax_Syntax.sigmeta);
            FStarC_Syntax_Syntax.sigattrs =
              (s1.FStarC_Syntax_Syntax.sigattrs);
            FStarC_Syntax_Syntax.sigopens_and_abbrevs =
              (s1.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
            FStarC_Syntax_Syntax.sigopts = (s1.FStarC_Syntax_Syntax.sigopts)
          }
      | FStarC_Syntax_Syntax.Sig_effect_abbrev
          { FStarC_Syntax_Syntax.lid4 = lid;
            FStarC_Syntax_Syntax.us4 = univ_names;
            FStarC_Syntax_Syntax.bs2 = binders;
            FStarC_Syntax_Syntax.comp1 = comp;
            FStarC_Syntax_Syntax.cflags = flags;_}
          ->
          let uu___ = elim_uvars_aux_c env1 univ_names binders comp in
          (match uu___ with
           | (univ_names1, binders1, comp1) ->
               {
                 FStarC_Syntax_Syntax.sigel =
                   (FStarC_Syntax_Syntax.Sig_effect_abbrev
                      {
                        FStarC_Syntax_Syntax.lid4 = lid;
                        FStarC_Syntax_Syntax.us4 = univ_names1;
                        FStarC_Syntax_Syntax.bs2 = binders1;
                        FStarC_Syntax_Syntax.comp1 = comp1;
                        FStarC_Syntax_Syntax.cflags = flags
                      });
                 FStarC_Syntax_Syntax.sigrng =
                   (s1.FStarC_Syntax_Syntax.sigrng);
                 FStarC_Syntax_Syntax.sigquals =
                   (s1.FStarC_Syntax_Syntax.sigquals);
                 FStarC_Syntax_Syntax.sigmeta =
                   (s1.FStarC_Syntax_Syntax.sigmeta);
                 FStarC_Syntax_Syntax.sigattrs =
                   (s1.FStarC_Syntax_Syntax.sigattrs);
                 FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                   (s1.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                 FStarC_Syntax_Syntax.sigopts =
                   (s1.FStarC_Syntax_Syntax.sigopts)
               })
      | FStarC_Syntax_Syntax.Sig_pragma uu___ -> s1
      | FStarC_Syntax_Syntax.Sig_fail uu___ -> s1
      | FStarC_Syntax_Syntax.Sig_splice uu___ -> s1
      | FStarC_Syntax_Syntax.Sig_polymonadic_bind
          { FStarC_Syntax_Syntax.m_lid = m; FStarC_Syntax_Syntax.n_lid = n;
            FStarC_Syntax_Syntax.p_lid = p;
            FStarC_Syntax_Syntax.tm3 = (us_t, t);
            FStarC_Syntax_Syntax.typ = (us_ty, ty);
            FStarC_Syntax_Syntax.kind1 = k;_}
          ->
          let uu___ = elim_uvars_aux_t env1 us_t [] t in
          (match uu___ with
           | (us_t1, uu___1, t1) ->
               let uu___2 = elim_uvars_aux_t env1 us_ty [] ty in
               (match uu___2 with
                | (us_ty1, uu___3, ty1) ->
                    {
                      FStarC_Syntax_Syntax.sigel =
                        (FStarC_Syntax_Syntax.Sig_polymonadic_bind
                           {
                             FStarC_Syntax_Syntax.m_lid = m;
                             FStarC_Syntax_Syntax.n_lid = n;
                             FStarC_Syntax_Syntax.p_lid = p;
                             FStarC_Syntax_Syntax.tm3 = (us_t1, t1);
                             FStarC_Syntax_Syntax.typ = (us_ty1, ty1);
                             FStarC_Syntax_Syntax.kind1 = k
                           });
                      FStarC_Syntax_Syntax.sigrng =
                        (s1.FStarC_Syntax_Syntax.sigrng);
                      FStarC_Syntax_Syntax.sigquals =
                        (s1.FStarC_Syntax_Syntax.sigquals);
                      FStarC_Syntax_Syntax.sigmeta =
                        (s1.FStarC_Syntax_Syntax.sigmeta);
                      FStarC_Syntax_Syntax.sigattrs =
                        (s1.FStarC_Syntax_Syntax.sigattrs);
                      FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                        (s1.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                      FStarC_Syntax_Syntax.sigopts =
                        (s1.FStarC_Syntax_Syntax.sigopts)
                    }))
      | FStarC_Syntax_Syntax.Sig_polymonadic_subcomp
          { FStarC_Syntax_Syntax.m_lid1 = m; FStarC_Syntax_Syntax.n_lid1 = n;
            FStarC_Syntax_Syntax.tm4 = (us_t, t);
            FStarC_Syntax_Syntax.typ1 = (us_ty, ty);
            FStarC_Syntax_Syntax.kind2 = k;_}
          ->
          let uu___ = elim_uvars_aux_t env1 us_t [] t in
          (match uu___ with
           | (us_t1, uu___1, t1) ->
               let uu___2 = elim_uvars_aux_t env1 us_ty [] ty in
               (match uu___2 with
                | (us_ty1, uu___3, ty1) ->
                    {
                      FStarC_Syntax_Syntax.sigel =
                        (FStarC_Syntax_Syntax.Sig_polymonadic_subcomp
                           {
                             FStarC_Syntax_Syntax.m_lid1 = m;
                             FStarC_Syntax_Syntax.n_lid1 = n;
                             FStarC_Syntax_Syntax.tm4 = (us_t1, t1);
                             FStarC_Syntax_Syntax.typ1 = (us_ty1, ty1);
                             FStarC_Syntax_Syntax.kind2 = k
                           });
                      FStarC_Syntax_Syntax.sigrng =
                        (s1.FStarC_Syntax_Syntax.sigrng);
                      FStarC_Syntax_Syntax.sigquals =
                        (s1.FStarC_Syntax_Syntax.sigquals);
                      FStarC_Syntax_Syntax.sigmeta =
                        (s1.FStarC_Syntax_Syntax.sigmeta);
                      FStarC_Syntax_Syntax.sigattrs =
                        (s1.FStarC_Syntax_Syntax.sigattrs);
                      FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                        (s1.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                      FStarC_Syntax_Syntax.sigopts =
                        (s1.FStarC_Syntax_Syntax.sigopts)
                    }))
let (erase_universes :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun env1 ->
    fun t ->
      normalize
        [FStarC_TypeChecker_Env.EraseUniverses;
        FStarC_TypeChecker_Env.AllowUnboundUniverses] env1 t
let (unfold_head_once :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun t ->
      let aux f us args =
        let uu___ =
          FStarC_TypeChecker_Env.lookup_nonrec_definition
            [FStarC_TypeChecker_Env.Unfold
               FStarC_Syntax_Syntax.delta_constant] env1
            (f.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
        match uu___ with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu___1 =
              FStarC_TypeChecker_Env.inst_tscheme_with head_def_ts us in
            (match uu___1 with
             | (uu___2, head_def) ->
                 let t' =
                   FStarC_Syntax_Syntax.mk_Tm_app head_def args
                     t.FStarC_Syntax_Syntax.pos in
                 let t'1 =
                   normalize
                     [FStarC_TypeChecker_Env.Beta;
                     FStarC_TypeChecker_Env.Iota] env1 t' in
                 FStar_Pervasives_Native.Some t'1) in
      let uu___ = FStarC_Syntax_Util.head_and_args t in
      match uu___ with
      | (head, args) ->
          let uu___1 =
            let uu___2 = FStarC_Syntax_Subst.compress head in
            uu___2.FStarC_Syntax_Syntax.n in
          (match uu___1 with
           | FStarC_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStarC_Syntax_Syntax.Tm_uinst
               ({ FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar fv;
                  FStarC_Syntax_Syntax.pos = uu___2;
                  FStarC_Syntax_Syntax.vars = uu___3;
                  FStarC_Syntax_Syntax.hash_code = uu___4;_},
                us)
               -> aux fv us args
           | uu___2 -> FStar_Pervasives_Native.None)
let (get_n_binders' :
  FStarC_TypeChecker_Env.env ->
    FStarC_TypeChecker_Env.step Prims.list ->
      Prims.int ->
        FStarC_Syntax_Syntax.term ->
          (FStarC_Syntax_Syntax.binder Prims.list *
            FStarC_Syntax_Syntax.comp))
  =
  fun env1 ->
    fun steps ->
      fun n ->
        fun t ->
          let rec aux retry n1 t1 =
            let uu___ = FStarC_Syntax_Util.arrow_formals_comp t1 in
            match uu___ with
            | (bs, c) ->
                let len = FStarC_Compiler_List.length bs in
                (match (bs, c) with
                 | ([], uu___1) when retry ->
                     let uu___2 = unfold_whnf' steps env1 t1 in
                     aux false n1 uu___2
                 | ([], uu___1) when Prims.op_Negation retry -> (bs, c)
                 | (bs1, c1) when len = n1 -> (bs1, c1)
                 | (bs1, c1) when len > n1 ->
                     let uu___1 = FStarC_Compiler_List.splitAt n1 bs1 in
                     (match uu___1 with
                      | (bs_l, bs_r) ->
                          let uu___2 =
                            let uu___3 = FStarC_Syntax_Util.arrow bs_r c1 in
                            FStarC_Syntax_Syntax.mk_Total uu___3 in
                          (bs_l, uu___2))
                 | (bs1, c1) when
                     ((len < n1) && (FStarC_Syntax_Util.is_total_comp c1)) &&
                       (let uu___1 = FStarC_Syntax_Util.has_decreases c1 in
                        Prims.op_Negation uu___1)
                     ->
                     let uu___1 =
                       aux true (n1 - len)
                         (FStarC_Syntax_Util.comp_result c1) in
                     (match uu___1 with
                      | (bs', c') ->
                          ((FStarC_Compiler_List.op_At bs1 bs'), c'))
                 | (bs1, c1) -> (bs1, c1)) in
          aux true n t
let (get_n_binders :
  FStarC_TypeChecker_Env.env ->
    Prims.int ->
      FStarC_Syntax_Syntax.term ->
        (FStarC_Syntax_Syntax.binder Prims.list * FStarC_Syntax_Syntax.comp))
  = fun env1 -> fun n -> fun t -> get_n_binders' env1 [] n t
let (uu___0 : unit) =
  FStarC_Compiler_Effect.op_Colon_Equals __get_n_binders get_n_binders'
let (maybe_unfold_head_fv :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun head ->
      let fv_us_opt =
        let uu___ =
          let uu___1 = FStarC_Syntax_Subst.compress head in
          uu___1.FStarC_Syntax_Syntax.n in
        match uu___ with
        | FStarC_Syntax_Syntax.Tm_uinst
            ({ FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar fv;
               FStarC_Syntax_Syntax.pos = uu___1;
               FStarC_Syntax_Syntax.vars = uu___2;
               FStarC_Syntax_Syntax.hash_code = uu___3;_},
             us)
            -> FStar_Pervasives_Native.Some (fv, us)
        | FStarC_Syntax_Syntax.Tm_fvar fv ->
            FStar_Pervasives_Native.Some (fv, [])
        | uu___1 -> FStar_Pervasives_Native.None in
      match fv_us_opt with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (fv, us) ->
          let uu___ =
            FStarC_TypeChecker_Env.lookup_nonrec_definition
              [FStarC_TypeChecker_Env.Unfold
                 FStarC_Syntax_Syntax.delta_constant] env1
              (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
          (match uu___ with
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (us_formals, defn) ->
               let subst = FStarC_TypeChecker_Env.mk_univ_subst us_formals us in
               let uu___1 = FStarC_Syntax_Subst.subst subst defn in
               FStar_Pervasives_Native.Some uu___1)
let rec (maybe_unfold_aux :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun t ->
      let uu___ =
        let uu___1 = FStarC_Syntax_Subst.compress t in
        uu___1.FStarC_Syntax_Syntax.n in
      match uu___ with
      | FStarC_Syntax_Syntax.Tm_match
          { FStarC_Syntax_Syntax.scrutinee = t0;
            FStarC_Syntax_Syntax.ret_opt = ret_opt;
            FStarC_Syntax_Syntax.brs = brs;
            FStarC_Syntax_Syntax.rc_opt1 = rc_opt;_}
          ->
          let uu___1 = maybe_unfold_aux env1 t0 in
          FStarC_Compiler_Util.map_option
            (fun t01 ->
               FStarC_Syntax_Syntax.mk
                 (FStarC_Syntax_Syntax.Tm_match
                    {
                      FStarC_Syntax_Syntax.scrutinee = t01;
                      FStarC_Syntax_Syntax.ret_opt = ret_opt;
                      FStarC_Syntax_Syntax.brs = brs;
                      FStarC_Syntax_Syntax.rc_opt1 = rc_opt
                    }) t.FStarC_Syntax_Syntax.pos) uu___1
      | FStarC_Syntax_Syntax.Tm_fvar uu___1 -> maybe_unfold_head_fv env1 t
      | FStarC_Syntax_Syntax.Tm_uinst uu___1 -> maybe_unfold_head_fv env1 t
      | uu___1 ->
          let uu___2 = FStarC_Syntax_Util.leftmost_head_and_args t in
          (match uu___2 with
           | (head, args) ->
               if args = []
               then maybe_unfold_head_fv env1 head
               else
                 (let uu___4 = maybe_unfold_aux env1 head in
                  match uu___4 with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some head1 ->
                      let uu___5 =
                        FStarC_Syntax_Syntax.mk_Tm_app head1 args
                          t.FStarC_Syntax_Syntax.pos in
                      FStar_Pervasives_Native.Some uu___5))
let (maybe_unfold_head :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun t ->
      let uu___ = maybe_unfold_aux env1 t in
      FStarC_Compiler_Util.map_option
        (normalize
           [FStarC_TypeChecker_Env.Beta;
           FStarC_TypeChecker_Env.Iota;
           FStarC_TypeChecker_Env.Weak;
           FStarC_TypeChecker_Env.HNF] env1) uu___