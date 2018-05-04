open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
let (guard_of_guard_formula :
  FStar_TypeChecker_Common.guard_formula -> FStar_TypeChecker_Env.guard_t) =
  fun g  ->
    {
      FStar_TypeChecker_Env.guard_f = g;
      FStar_TypeChecker_Env.deferred = [];
      FStar_TypeChecker_Env.univ_ineqs = ([], []);
      FStar_TypeChecker_Env.implicits = []
    }
  
let (guard_form :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Common.guard_formula) =
  fun g  -> g.FStar_TypeChecker_Env.guard_f 
let (is_trivial : FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Env.deferred = [];
        FStar_TypeChecker_Env.univ_ineqs = uu____39;
        FStar_TypeChecker_Env.implicits = uu____40;_} -> true
    | uu____65 -> false
  
let (trivial_guard : FStar_TypeChecker_Env.guard_t) =
  {
    FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial;
    FStar_TypeChecker_Env.deferred = [];
    FStar_TypeChecker_Env.univ_ineqs = ([], []);
    FStar_TypeChecker_Env.implicits = []
  } 
let (abstract_guard_n :
  FStar_Syntax_Syntax.binder Prims.list ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun bs  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let f' =
            FStar_Syntax_Util.abs bs f
              (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
             in
          let uu___152_102 = g  in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___152_102.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___152_102.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___152_102.FStar_TypeChecker_Env.implicits)
          }
  
let (abstract_guard :
  FStar_Syntax_Syntax.binder ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun b  -> fun g  -> abstract_guard_n [b] g 
let (def_check_vars_in_set :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv FStar_Util.set ->
        FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun vset  ->
        fun t  ->
          let uu____137 = FStar_Options.defensive ()  in
          if uu____137
          then
            let s = FStar_Syntax_Free.names t  in
            let uu____141 =
              let uu____142 =
                let uu____143 = FStar_Util.set_difference s vset  in
                FStar_All.pipe_left FStar_Util.set_is_empty uu____143  in
              Prims.op_Negation uu____142  in
            (if uu____141
             then
               let uu____148 =
                 let uu____153 =
                   let uu____154 = FStar_Syntax_Print.term_to_string t  in
                   let uu____155 =
                     let uu____156 = FStar_Util.set_elements s  in
                     FStar_All.pipe_right uu____156
                       (FStar_Syntax_Print.bvs_to_string ",\n\t")
                      in
                   FStar_Util.format3
                     "Internal: term is not closed (%s).\nt = (%s)\nFVs = (%s)\n"
                     msg uu____154 uu____155
                    in
                 (FStar_Errors.Warning_Defensive, uu____153)  in
               FStar_Errors.log_issue rng uu____148
             else ())
          else ()
  
let (def_check_closed :
  FStar_Range.range -> Prims.string -> FStar_Syntax_Syntax.term -> unit) =
  fun rng  ->
    fun msg  ->
      fun t  ->
        let uu____178 =
          let uu____179 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____179  in
        if uu____178
        then ()
        else def_check_vars_in_set rng msg FStar_Syntax_Free.empty t
  
let (def_check_closed_in :
  FStar_Range.range ->
    Prims.string ->
      FStar_Syntax_Syntax.bv Prims.list -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun l  ->
        fun t  ->
          let uu____205 =
            let uu____206 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____206  in
          if uu____205
          then ()
          else
            (let uu____208 = FStar_Util.as_set l FStar_Syntax_Syntax.order_bv
                in
             def_check_vars_in_set rng msg uu____208 t)
  
let (def_check_closed_in_env :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun rng  ->
    fun msg  ->
      fun e  ->
        fun t  ->
          let uu____231 =
            let uu____232 = FStar_Options.defensive ()  in
            Prims.op_Negation uu____232  in
          if uu____231
          then ()
          else
            (let uu____234 = FStar_TypeChecker_Env.bound_vars e  in
             def_check_closed_in rng msg uu____234 t)
  
let (apply_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t)
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___153_248 = g  in
          let uu____249 =
            let uu____250 =
              let uu____251 =
                let uu____258 =
                  let uu____259 =
                    let uu____274 =
                      let uu____283 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____283]  in
                    (f, uu____274)  in
                  FStar_Syntax_Syntax.Tm_app uu____259  in
                FStar_Syntax_Syntax.mk uu____258  in
              uu____251 FStar_Pervasives_Native.None
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_17  -> FStar_TypeChecker_Common.NonTrivial _0_17)
              uu____250
             in
          {
            FStar_TypeChecker_Env.guard_f = uu____249;
            FStar_TypeChecker_Env.deferred =
              (uu___153_248.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___153_248.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___153_248.FStar_TypeChecker_Env.implicits)
          }
  
let (map_guard :
  FStar_TypeChecker_Env.guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      FStar_TypeChecker_Env.guard_t)
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___154_331 = g  in
          let uu____332 =
            let uu____333 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____333  in
          {
            FStar_TypeChecker_Env.guard_f = uu____332;
            FStar_TypeChecker_Env.deferred =
              (uu___154_331.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___154_331.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___154_331.FStar_TypeChecker_Env.implicits)
          }
  
let (trivial : FStar_TypeChecker_Common.guard_formula -> unit) =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____339 -> failwith "impossible"
  
let (conj_guard_f :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g) -> g
      | (g,FStar_TypeChecker_Common.Trivial ) -> g
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let uu____354 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____354
  
let (check_trivial :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_TypeChecker_Common.guard_formula)
  =
  fun t  ->
    let uu____364 =
      let uu____365 = FStar_Syntax_Util.unmeta t  in
      uu____365.FStar_Syntax_Syntax.n  in
    match uu____364 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____369 -> FStar_TypeChecker_Common.NonTrivial t
  
let (imp_guard_f :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g) -> g
      | (g,FStar_TypeChecker_Common.Trivial ) ->
          FStar_TypeChecker_Common.Trivial
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let imp = FStar_Syntax_Util.mk_imp f1 f2  in check_trivial imp
  
let (binop_guard :
  (FStar_TypeChecker_Common.guard_formula ->
     FStar_TypeChecker_Common.guard_formula ->
       FStar_TypeChecker_Common.guard_formula)
    ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun f  ->
    fun g1  ->
      fun g2  ->
        let uu____410 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f
           in
        {
          FStar_TypeChecker_Env.guard_f = uu____410;
          FStar_TypeChecker_Env.deferred =
            (FStar_List.append g1.FStar_TypeChecker_Env.deferred
               g2.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            ((FStar_List.append
                (FStar_Pervasives_Native.fst
                   g1.FStar_TypeChecker_Env.univ_ineqs)
                (FStar_Pervasives_Native.fst
                   g2.FStar_TypeChecker_Env.univ_ineqs)),
              (FStar_List.append
                 (FStar_Pervasives_Native.snd
                    g1.FStar_TypeChecker_Env.univ_ineqs)
                 (FStar_Pervasives_Native.snd
                    g2.FStar_TypeChecker_Env.univ_ineqs)));
          FStar_TypeChecker_Env.implicits =
            (FStar_List.append g1.FStar_TypeChecker_Env.implicits
               g2.FStar_TypeChecker_Env.implicits)
        }
  
let (conj_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun g1  -> fun g2  -> binop_guard conj_guard_f g1 g2 
let (imp_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun g1  -> fun g2  -> binop_guard imp_guard_f g1 g2 
let (close_guard_univs :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun us  ->
    fun bs  ->
      fun g  ->
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let f1 =
              FStar_List.fold_right2
                (fun u  ->
                   fun b  ->
                     fun f1  ->
                       let uu____497 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____497
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___155_499 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___155_499.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___155_499.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___155_499.FStar_TypeChecker_Env.implicits)
            }
  
let (close_forall :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun bs  ->
      fun f  ->
        FStar_List.fold_right
          (fun b  ->
             fun f1  ->
               let uu____540 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____540
               then f1
               else
                 (let u =
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  FStar_Syntax_Util.mk_forall u
                    (FStar_Pervasives_Native.fst b) f1)) bs f
  
let (close_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun binders  ->
      fun g  ->
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___156_559 = g  in
            let uu____560 =
              let uu____561 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____561  in
            {
              FStar_TypeChecker_Env.guard_f = uu____560;
              FStar_TypeChecker_Env.deferred =
                (uu___156_559.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___156_559.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___156_559.FStar_TypeChecker_Env.implicits)
            }
  
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____590 -> false
  
let (__proj__TERM__item___0 :
  uvi ->
    (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____620 -> false
  
let (__proj__UNIV__item___0 :
  uvi ->
    (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UNIV _0 -> _0 
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs ;
  wl_deferred:
    (Prims.int,Prims.string,FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list
    ;
  ctr: Prims.int ;
  defer_ok: Prims.bool ;
  smt_ok: Prims.bool ;
  tcenv: FStar_TypeChecker_Env.env ;
  wl_implicits: FStar_TypeChecker_Env.implicits }[@@deriving show]
let (__proj__Mkworklist__item__attempting :
  worklist -> FStar_TypeChecker_Common.probs) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;
        wl_implicits = __fname__wl_implicits;_} -> __fname__attempting
  
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int,Prims.string,FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;
        wl_implicits = __fname__wl_implicits;_} -> __fname__wl_deferred
  
let (__proj__Mkworklist__item__ctr : worklist -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;
        wl_implicits = __fname__wl_implicits;_} -> __fname__ctr
  
let (__proj__Mkworklist__item__defer_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;
        wl_implicits = __fname__wl_implicits;_} -> __fname__defer_ok
  
let (__proj__Mkworklist__item__smt_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;
        wl_implicits = __fname__wl_implicits;_} -> __fname__smt_ok
  
let (__proj__Mkworklist__item__tcenv : worklist -> FStar_TypeChecker_Env.env)
  =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;
        wl_implicits = __fname__wl_implicits;_} -> __fname__tcenv
  
let (__proj__Mkworklist__item__wl_implicits :
  worklist -> FStar_TypeChecker_Env.implicits) =
  fun projectee  ->
    match projectee with
    | { attempting = __fname__attempting; wl_deferred = __fname__wl_deferred;
        ctr = __fname__ctr; defer_ok = __fname__defer_ok;
        smt_ok = __fname__smt_ok; tcenv = __fname__tcenv;
        wl_implicits = __fname__wl_implicits;_} -> __fname__wl_implicits
  
let (new_uvar :
  Prims.string ->
    worklist ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.binding Prims.list ->
          (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
            FStar_Pervasives_Native.tuple2 Prims.list ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
              Prims.bool ->
                (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term,
                  worklist) FStar_Pervasives_Native.tuple3)
  =
  fun reason  ->
    fun wl  ->
      fun r  ->
        fun gamma  ->
          fun binders  ->
            fun k  ->
              fun should_check  ->
                let ctx_uvar =
                  let uu____907 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____907;
                    FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                    FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                    FStar_Syntax_Syntax.ctx_uvar_typ = k;
                    FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                    FStar_Syntax_Syntax.ctx_uvar_should_check = should_check;
                    FStar_Syntax_Syntax.ctx_uvar_range = r
                  }  in
                FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r
                  true gamma binders;
                (let t =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_uvar (ctx_uvar, []))
                     FStar_Pervasives_Native.None r
                    in
                 (ctx_uvar, t,
                   (let uu___157_925 = wl  in
                    {
                      attempting = (uu___157_925.attempting);
                      wl_deferred = (uu___157_925.wl_deferred);
                      ctr = (uu___157_925.ctr);
                      defer_ok = (uu___157_925.defer_ok);
                      smt_ok = (uu___157_925.smt_ok);
                      tcenv = (uu___157_925.tcenv);
                      wl_implicits = ((reason, t, ctx_uvar, r, should_check)
                        :: (wl.wl_implicits))
                    })))
  
let (copy_uvar :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      worklist ->
        (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term,worklist)
          FStar_Pervasives_Native.tuple3)
  =
  fun u  ->
    fun t  ->
      fun wl  ->
        new_uvar u.FStar_Syntax_Syntax.ctx_uvar_reason wl
          u.FStar_Syntax_Syntax.ctx_uvar_range
          u.FStar_Syntax_Syntax.ctx_uvar_gamma
          u.FStar_Syntax_Syntax.ctx_uvar_binders t
          u.FStar_Syntax_Syntax.ctx_uvar_should_check
  
type solution =
  | Success of
  (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
  FStar_Pervasives_Native.tuple2 
  | Failed of (FStar_TypeChecker_Common.prob,Prims.string)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____989 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____1019 -> false
  
let (__proj__Failed__item___0 :
  solution ->
    (FStar_TypeChecker_Common.prob,Prims.string)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT [@@deriving show]
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____1044 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____1050 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____1056 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
[@@deriving show]
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
[@@deriving show]
type 'a problem_t = 'a FStar_TypeChecker_Common.problem[@@deriving show]
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___119_1071  ->
    match uu___119_1071 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  -> FStar_Syntax_Print.term_to_string t 
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___120_1086  ->
      match uu___120_1086 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1090 =
            let uu____1093 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____1094 =
              let uu____1097 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____1098 =
                let uu____1101 =
                  let uu____1104 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  let uu____1105 =
                    let uu____1108 =
                      term_to_string p.FStar_TypeChecker_Common.logical_guard
                       in
                    let uu____1109 =
                      let uu____1112 =
                        match p.FStar_TypeChecker_Common.element with
                        | FStar_Pervasives_Native.None  -> "none"
                        | FStar_Pervasives_Native.Some t -> term_to_string t
                         in
                      [uu____1112]  in
                    uu____1108 :: uu____1109  in
                  uu____1104 :: uu____1105  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____1101
                 in
              uu____1097 :: uu____1098  in
            uu____1093 :: uu____1094  in
          FStar_Util.format
            "\n%s:\t%s \n\t\t%s\n\t%s\n\twith guard %s\n\telement= %s\n"
            uu____1090
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1117 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____1118 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____1119 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____1117 uu____1118
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1119
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___121_1129  ->
      match uu___121_1129 with
      | UNIV (u,t) ->
          let x =
            let uu____1133 = FStar_Options.hide_uvar_nums ()  in
            if uu____1133
            then "?"
            else
              (let uu____1135 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____1135 FStar_Util.string_of_int)
             in
          let uu____1136 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____1136
      | TERM (u,t) ->
          let x =
            let uu____1140 = FStar_Options.hide_uvar_nums ()  in
            if uu____1140
            then "?"
            else
              (let uu____1142 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____1142 FStar_Util.string_of_int)
             in
          let uu____1143 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____1143
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____1158 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____1158 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1172 =
      let uu____1175 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1175
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1172 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1188 .
    (FStar_Syntax_Syntax.term,'Auu____1188) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1206 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1224  ->
              match uu____1224 with
              | (x,uu____1230) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1206 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
    let uu____1238 =
      let uu____1239 = FStar_Options.eager_inference ()  in
      Prims.op_Negation uu____1239  in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____1238;
      smt_ok = true;
      tcenv = env;
      wl_implicits = []
    }
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___158_1271 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___158_1271.wl_deferred);
          ctr = (uu___158_1271.ctr);
          defer_ok = (uu___158_1271.defer_ok);
          smt_ok;
          tcenv = (uu___158_1271.tcenv);
          wl_implicits = (uu___158_1271.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1278 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1278,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___159_1301 = empty_worklist env  in
      let uu____1302 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1302;
        wl_deferred = (uu___159_1301.wl_deferred);
        ctr = (uu___159_1301.ctr);
        defer_ok = (uu___159_1301.defer_ok);
        smt_ok = (uu___159_1301.smt_ok);
        tcenv = (uu___159_1301.tcenv);
        wl_implicits = (uu___159_1301.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___160_1322 = wl  in
        {
          attempting = (uu___160_1322.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___160_1322.ctr);
          defer_ok = (uu___160_1322.defer_ok);
          smt_ok = (uu___160_1322.smt_ok);
          tcenv = (uu___160_1322.tcenv);
          wl_implicits = (uu___160_1322.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      let uu___161_1343 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___161_1343.wl_deferred);
        ctr = (uu___161_1343.ctr);
        defer_ok = (uu___161_1343.defer_ok);
        smt_ok = (uu___161_1343.smt_ok);
        tcenv = (uu___161_1343.tcenv);
        wl_implicits = (uu___161_1343.wl_implicits)
      }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1360 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1360
         then
           let uu____1361 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1361
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___122_1367  ->
    match uu___122_1367 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1372 .
    'Auu____1372 FStar_TypeChecker_Common.problem ->
      'Auu____1372 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___162_1384 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___162_1384.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___162_1384.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___162_1384.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___162_1384.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___162_1384.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___162_1384.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___162_1384.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1391 .
    'Auu____1391 FStar_TypeChecker_Common.problem ->
      'Auu____1391 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___123_1408  ->
    match uu___123_1408 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_18  -> FStar_TypeChecker_Common.TProb _0_18)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_19  -> FStar_TypeChecker_Common.CProb _0_19)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___124_1423  ->
    match uu___124_1423 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___163_1429 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___163_1429.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___163_1429.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___163_1429.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___163_1429.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___163_1429.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___163_1429.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___163_1429.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___163_1429.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___163_1429.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___164_1437 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___164_1437.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___164_1437.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___164_1437.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___164_1437.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___164_1437.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___164_1437.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___164_1437.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___164_1437.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___164_1437.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___125_1449  ->
      match uu___125_1449 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___126_1454  ->
    match uu___126_1454 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___127_1465  ->
    match uu___127_1465 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___128_1478  ->
    match uu___128_1478 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___129_1491  ->
    match uu___129_1491 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___130_1502  ->
    match uu___130_1502 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.ctx_uvar)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___131_1517  ->
    match uu___131_1517 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1536 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv,'Auu____1536) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1564 =
          let uu____1565 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1565  in
        if uu____1564
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1599)::bs ->
                 (def_check_closed_in rng msg prev
                    bv.FStar_Syntax_Syntax.sort;
                  aux (FStar_List.append prev [bv]) bs)
              in
           aux [] r)
  
let (p_scope :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun prob  ->
    let r =
      match prob with
      | FStar_TypeChecker_Common.TProb p ->
          FStar_List.append
            (FStar_Pervasives_Native.snd
               p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            (FStar_Pervasives_Native.fst
               p.FStar_TypeChecker_Common.logical_guard_uvar)
      | FStar_TypeChecker_Common.CProb p ->
          FStar_List.append
            (FStar_Pervasives_Native.snd
               p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            (FStar_Pervasives_Native.fst
               p.FStar_TypeChecker_Common.logical_guard_uvar)
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1666 =
          let uu____1667 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1667  in
        if uu____1666
        then ()
        else
          (let uu____1669 =
             let uu____1672 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1672
              in
           def_check_closed_in (p_loc prob) msg uu____1669 phi)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      (let uu____1702 =
         let uu____1703 = FStar_Options.defensive ()  in
         Prims.op_Negation uu____1703  in
       if uu____1702
       then ()
       else
         (let uu____1705 = p_scope prob  in
          def_scope_wf (Prims.strcat msg ".scope") (p_loc prob) uu____1705));
      def_check_scoped (Prims.strcat msg ".guard") prob (p_guard prob);
      (match prob with
       | FStar_TypeChecker_Common.TProb p ->
           (def_check_scoped (Prims.strcat msg ".lhs") prob
              p.FStar_TypeChecker_Common.lhs;
            def_check_scoped (Prims.strcat msg ".rhs") prob
              p.FStar_TypeChecker_Common.rhs)
       | uu____1717 -> ())
  
let mk_eq2 :
  'Auu____1729 .
    worklist ->
      'Auu____1729 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term,worklist)
              FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun prob  ->
      fun t1  ->
        fun t2  ->
          let uu____1758 = FStar_Syntax_Util.type_u ()  in
          match uu____1758 with
          | (t_type,u) ->
              let binders = FStar_TypeChecker_Env.all_binders wl.tcenv  in
              let uu____1770 =
                new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                  (wl.tcenv).FStar_TypeChecker_Env.gamma binders t_type false
                 in
              (match uu____1770 with
               | (uu____1781,tt,wl1) ->
                   let uu____1784 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                   (uu____1784, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___132_1789  ->
    match uu___132_1789 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_20  -> FStar_TypeChecker_Common.TProb _0_20) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_21  -> FStar_TypeChecker_Common.CProb _0_21) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1805 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1805 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1817  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____1915 .
    worklist ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____1915 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____1915 ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____1915 FStar_TypeChecker_Common.problem,worklist)
                      FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun scope  ->
      fun orig  ->
        fun lhs  ->
          fun rel  ->
            fun rhs  ->
              fun elt  ->
                fun reason  ->
                  let guard_ty =
                    let uu____1981 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_Syntax_Util.arrow scope uu____1981  in
                  let uu____1984 =
                    let uu____1991 =
                      FStar_TypeChecker_Env.all_binders wl.tcenv  in
                    new_uvar
                      (Prims.strcat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange
                      (wl.tcenv).FStar_TypeChecker_Env.gamma uu____1991
                      guard_ty false
                     in
                  match uu____1984 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match scope with
                        | [] -> lg
                        | uu____2012 ->
                            let uu____2019 =
                              let uu____2024 =
                                FStar_List.map
                                  (fun uu____2037  ->
                                     match uu____2037 with
                                     | (x,i) ->
                                         let uu____2048 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         (uu____2048, i)) scope
                                 in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2024  in
                            uu____2019 FStar_Pervasives_Native.None
                              lg.FStar_Syntax_Syntax.pos
                         in
                      let uu____2051 =
                        let uu____2054 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2054;
                          FStar_TypeChecker_Common.lhs = lhs;
                          FStar_TypeChecker_Common.relation = rel;
                          FStar_TypeChecker_Common.rhs = rhs;
                          FStar_TypeChecker_Common.element = elt;
                          FStar_TypeChecker_Common.logical_guard = lg1;
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (scope, ctx_uvar);
                          FStar_TypeChecker_Common.reason = (reason ::
                            (p_reason orig));
                          FStar_TypeChecker_Common.loc = (p_loc orig);
                          FStar_TypeChecker_Common.rank =
                            FStar_Pervasives_Native.None
                        }  in
                      (uu____2051, wl1)
  
let (mk_t_problem :
  worklist ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_TypeChecker_Common.prob ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Common.rel ->
            FStar_Syntax_Syntax.typ ->
              FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
                Prims.string ->
                  (FStar_TypeChecker_Common.prob,worklist)
                    FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun scope  ->
      fun orig  ->
        fun lhs  ->
          fun rel  ->
            fun rhs  ->
              fun elt  ->
                fun reason  ->
                  let uu____2117 =
                    mk_problem wl scope orig lhs rel rhs elt reason  in
                  match uu____2117 with
                  | (p,wl1) -> ((FStar_TypeChecker_Common.TProb p), wl1)
  
let (mk_c_problem :
  worklist ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_TypeChecker_Common.prob ->
        FStar_Syntax_Syntax.comp ->
          FStar_TypeChecker_Common.rel ->
            FStar_Syntax_Syntax.comp ->
              FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
                Prims.string ->
                  (FStar_TypeChecker_Common.prob,worklist)
                    FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun scope  ->
      fun orig  ->
        fun lhs  ->
          fun rel  ->
            fun rhs  ->
              fun elt  ->
                fun reason  ->
                  let uu____2194 =
                    mk_problem wl scope orig lhs rel rhs elt reason  in
                  match uu____2194 with
                  | (p,wl1) -> ((FStar_TypeChecker_Common.CProb p), wl1)
  
let new_problem :
  'Auu____2229 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2229 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2229 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2229 FStar_TypeChecker_Common.problem,worklist)
                      FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun env  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun subject  ->
              fun loc  ->
                fun reason  ->
                  let uu____2280 =
                    match subject with
                    | FStar_Pervasives_Native.None  ->
                        ([], FStar_Syntax_Util.ktype0,
                          FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some x ->
                        let bs =
                          let uu____2335 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2335]  in
                        let uu____2348 =
                          let uu____2351 =
                            FStar_Syntax_Syntax.mk_Total
                              FStar_Syntax_Util.ktype0
                             in
                          FStar_Syntax_Util.arrow bs uu____2351  in
                        let uu____2354 =
                          let uu____2357 = FStar_Syntax_Syntax.bv_to_name x
                             in
                          FStar_Pervasives_Native.Some uu____2357  in
                        (bs, uu____2348, uu____2354)
                     in
                  match uu____2280 with
                  | (bs,lg_ty,elt) ->
                      let uu____2397 =
                        let uu____2404 =
                          FStar_TypeChecker_Env.all_binders env  in
                        new_uvar
                          (Prims.strcat "new_problem: logical guard for "
                             reason)
                          (let uu___165_2412 = wl  in
                           {
                             attempting = (uu___165_2412.attempting);
                             wl_deferred = (uu___165_2412.wl_deferred);
                             ctr = (uu___165_2412.ctr);
                             defer_ok = (uu___165_2412.defer_ok);
                             smt_ok = (uu___165_2412.smt_ok);
                             tcenv = env;
                             wl_implicits = (uu___165_2412.wl_implicits)
                           }) loc env.FStar_TypeChecker_Env.gamma uu____2404
                          lg_ty false
                         in
                      (match uu____2397 with
                       | (ctx_uvar,lg,wl1) ->
                           let lg1 =
                             match elt with
                             | FStar_Pervasives_Native.None  -> lg
                             | FStar_Pervasives_Native.Some x ->
                                 let uu____2424 =
                                   let uu____2429 =
                                     let uu____2430 =
                                       FStar_Syntax_Syntax.as_arg x  in
                                     [uu____2430]  in
                                   FStar_Syntax_Syntax.mk_Tm_app lg
                                     uu____2429
                                    in
                                 uu____2424 FStar_Pervasives_Native.None loc
                              in
                           let uu____2451 =
                             let uu____2454 = next_pid ()  in
                             {
                               FStar_TypeChecker_Common.pid = uu____2454;
                               FStar_TypeChecker_Common.lhs = lhs;
                               FStar_TypeChecker_Common.relation = rel;
                               FStar_TypeChecker_Common.rhs = rhs;
                               FStar_TypeChecker_Common.element = elt;
                               FStar_TypeChecker_Common.logical_guard = lg1;
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (bs, ctx_uvar);
                               FStar_TypeChecker_Common.reason = [reason];
                               FStar_TypeChecker_Common.loc = loc;
                               FStar_TypeChecker_Common.rank =
                                 FStar_Pervasives_Native.None
                             }  in
                           (uu____2451, wl1))
  
let problem_using_guard :
  'Auu____2471 .
    FStar_TypeChecker_Common.prob ->
      'Auu____2471 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____2471 ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
              Prims.string -> 'Auu____2471 FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____2508 = next_pid ()  in
              {
                FStar_TypeChecker_Common.pid = uu____2508;
                FStar_TypeChecker_Common.lhs = lhs;
                FStar_TypeChecker_Common.relation = rel;
                FStar_TypeChecker_Common.rhs = rhs;
                FStar_TypeChecker_Common.element = elt;
                FStar_TypeChecker_Common.logical_guard = (p_guard orig);
                FStar_TypeChecker_Common.logical_guard_uvar =
                  (p_guard_uvar orig);
                FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
                FStar_TypeChecker_Common.loc = (p_loc orig);
                FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
              }
  
let guard_on_element :
  'Auu____2519 .
    worklist ->
      'Auu____2519 FStar_TypeChecker_Common.problem ->
        FStar_Syntax_Syntax.bv ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun wl  ->
    fun problem  ->
      fun x  ->
        fun phi  ->
          match problem.FStar_TypeChecker_Common.element with
          | FStar_Pervasives_Native.None  ->
              let u =
                (wl.tcenv).FStar_TypeChecker_Env.universe_of wl.tcenv
                  x.FStar_Syntax_Syntax.sort
                 in
              FStar_Syntax_Util.mk_forall u x phi
          | FStar_Pervasives_Native.Some e ->
              FStar_Syntax_Subst.subst [FStar_Syntax_Syntax.NT (x, e)] phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2569 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2569
        then
          let uu____2570 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2571 = prob_to_string env d  in
          let uu____2572 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2570 uu____2571 uu____2572 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2578 -> failwith "impossible"  in
           let uu____2579 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2591 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2592 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2591, uu____2592)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2596 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2597 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2596, uu____2597)
              in
           match uu____2579 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___133_2615  ->
            match uu___133_2615 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2627 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                (def_check_closed t.FStar_Syntax_Syntax.pos "commit" t;
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___134_2649  ->
           match uu___134_2649 with
           | UNIV uu____2652 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2659 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2659
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None)
  
let (find_univ_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___135_2683  ->
           match uu___135_2683 with
           | UNIV (u',t) ->
               let uu____2688 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2688
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2692 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2703 =
        let uu____2704 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____2704
         in
      FStar_Syntax_Subst.compress uu____2703
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2715 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____2715
  
let norm_arg :
  'Auu____2722 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2722) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2722)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2745 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2745, (FStar_Pervasives_Native.snd t))
  
let (sn_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____2786  ->
              match uu____2786 with
              | (x,imp) ->
                  let uu____2797 =
                    let uu___166_2798 = x  in
                    let uu____2799 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___166_2798.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___166_2798.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2799
                    }  in
                  (uu____2797, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2820 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2820
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2824 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2824
        | uu____2827 -> u2  in
      let uu____2828 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2828
  
let (base_and_refinement_maybe_delta :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term'
                                                            FStar_Syntax_Syntax.syntax)
                                    FStar_Pervasives_Native.tuple2
                                    FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2)
  =
  fun should_delta  ->
    fun env  ->
      fun t1  ->
        let norm_refinement env1 t =
          let steps =
            if should_delta
            then
              [FStar_TypeChecker_Normalize.Weak;
              FStar_TypeChecker_Normalize.HNF;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant]
            else
              [FStar_TypeChecker_Normalize.Weak;
              FStar_TypeChecker_Normalize.HNF]
             in
          FStar_TypeChecker_Normalize.normalize_refinement steps env1 t  in
        let rec aux norm1 t11 =
          let t12 = FStar_Syntax_Util.unmeta t11  in
          match t12.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm1
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____2942 = norm_refinement env t12  in
                 match uu____2942 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2957;
                     FStar_Syntax_Syntax.vars = uu____2958;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____2984 =
                       let uu____2985 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____2986 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____2985 uu____2986
                        in
                     failwith uu____2984)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3000 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3000
          | FStar_Syntax_Syntax.Tm_uinst uu____3001 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3036 =
                   let uu____3037 = FStar_Syntax_Subst.compress t1'  in
                   uu____3037.FStar_Syntax_Syntax.n  in
                 match uu____3036 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3052 -> aux true t1'
                 | uu____3059 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3074 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3103 =
                   let uu____3104 = FStar_Syntax_Subst.compress t1'  in
                   uu____3104.FStar_Syntax_Syntax.n  in
                 match uu____3103 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3119 -> aux true t1'
                 | uu____3126 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3141 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3184 =
                   let uu____3185 = FStar_Syntax_Subst.compress t1'  in
                   uu____3185.FStar_Syntax_Syntax.n  in
                 match uu____3184 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3200 -> aux true t1'
                 | uu____3207 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3222 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3237 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3252 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3267 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3282 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3309 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3340 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3361 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3382 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3409 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3446 ->
              let uu____3453 =
                let uu____3454 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3455 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3454 uu____3455
                 in
              failwith uu____3453
          | FStar_Syntax_Syntax.Tm_ascribed uu____3468 ->
              let uu____3495 =
                let uu____3496 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3497 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3496 uu____3497
                 in
              failwith uu____3495
          | FStar_Syntax_Syntax.Tm_delayed uu____3510 ->
              let uu____3535 =
                let uu____3536 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3537 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3536 uu____3537
                 in
              failwith uu____3535
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3550 =
                let uu____3551 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3552 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3551 uu____3552
                 in
              failwith uu____3550
           in
        let uu____3565 = whnf env t1  in aux false uu____3565
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let normalize_refinement :
  'Auu____3596 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____3596 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun steps  ->
    fun env  ->
      fun wl  ->
        fun t0  ->
          FStar_TypeChecker_Normalize.normalize_refinement steps env t0
  
let (unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun t  ->
      let uu____3627 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3627 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3663 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3663, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____3674 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____3674 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____3699 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____3699 with
          | (t_base,refinement) ->
              (match refinement with
               | FStar_Pervasives_Native.None  -> trivial_refinement t_base
               | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.bv,
                                                          FStar_Syntax_Syntax.term)
                                                          FStar_Pervasives_Native.tuple2
                                                          FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun uu____3776  ->
    match uu____3776 with
    | (t_base,refopt) ->
        let uu____3809 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3809 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____3849 =
      let uu____3852 =
        let uu____3855 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3878  ->
                  match uu____3878 with | (uu____3885,uu____3886,x) -> x))
           in
        FStar_List.append wl.attempting uu____3855  in
      FStar_List.map (wl_prob_to_string wl) uu____3852  in
    FStar_All.pipe_right uu____3849 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3[@@deriving show]
let flex_t_to_string :
  'Auu____3900 .
    ('Auu____3900,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____3911  ->
    match uu____3911 with
    | (uu____3918,c,args) ->
        let uu____3921 = print_ctx_uvar c  in
        let uu____3922 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____3921 uu____3922
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3928 = FStar_Syntax_Util.head_and_args t  in
    match uu____3928 with
    | (head1,_args) ->
        let uu____3965 =
          let uu____3966 = FStar_Syntax_Subst.compress head1  in
          uu____3966.FStar_Syntax_Syntax.n  in
        (match uu____3965 with
         | FStar_Syntax_Syntax.Tm_uvar uu____3969 -> true
         | uu____3976 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____3982 = FStar_Syntax_Util.head_and_args t  in
    match uu____3982 with
    | (head1,_args) ->
        let uu____4019 =
          let uu____4020 = FStar_Syntax_Subst.compress head1  in
          uu____4020.FStar_Syntax_Syntax.n  in
        (match uu____4019 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4024) -> u
         | uu____4029 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t,worklist) FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun wl  ->
      let uu____4052 = FStar_Syntax_Util.head_and_args t  in
      match uu____4052 with
      | (head1,args) ->
          let uu____4093 =
            let uu____4094 = FStar_Syntax_Subst.compress head1  in
            uu____4094.FStar_Syntax_Syntax.n  in
          (match uu____4093 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,[]) -> ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let dom_s =
                 FStar_All.pipe_right s
                   (FStar_List.collect
                      (fun uu___136_4129  ->
                         match uu___136_4129 with
                         | FStar_Syntax_Syntax.NT (x,uu____4133) ->
                             let uu____4138 = FStar_Syntax_Syntax.mk_binder x
                                in
                             [uu____4138]
                         | FStar_Syntax_Syntax.NM (x,uu____4140) ->
                             let uu____4141 = FStar_Syntax_Syntax.mk_binder x
                                in
                             [uu____4141]
                         | uu____4142 -> []))
                  in
               let uu____4143 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___137_4165  ->
                         match uu___137_4165 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let uu____4167 =
                               FStar_Util.for_some
                                 (fun y  ->
                                    FStar_Syntax_Syntax.bv_eq x
                                      (FStar_Pervasives_Native.fst y)) dom_s
                                in
                             Prims.op_Negation uu____4167
                         | uu____4178 -> true))
                  in
               (match uu____4143 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4200 =
                        FStar_List.map
                          (fun uu___138_4205  ->
                             match uu___138_4205 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 FStar_Syntax_Syntax.mk_binder x)
                          dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4200 FStar_List.rev  in
                    let uu____4215 =
                      let uu____4222 =
                        let uu____4229 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___139_4243  ->
                                  match uu___139_4243 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4247 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4247]
                                  | uu____4248 -> []))
                           in
                        FStar_All.pipe_right uu____4229 FStar_List.rev  in
                      let uu____4265 =
                        let uu____4268 =
                          let uu____4271 =
                            FStar_Syntax_Subst.subst s
                              uv.FStar_Syntax_Syntax.ctx_uvar_typ
                             in
                          FStar_Syntax_Syntax.mk_Total uu____4271  in
                        FStar_Syntax_Util.arrow dom_binders uu____4268  in
                      new_uvar
                        (Prims.strcat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4222 uu____4265
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                       in
                    (match uu____4215 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4298  ->
                                match uu____4298 with
                                | (x,i) ->
                                    let uu____4309 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4309, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4332  ->
                                match uu____4332 with
                                | (a,i) ->
                                    let uu____4343 =
                                      FStar_Syntax_Subst.subst s a  in
                                    (uu____4343, i)) args_sol
                            in
                         let all_args = FStar_List.append args_sol_s args  in
                         let t1 =
                           FStar_Syntax_Syntax.mk_Tm_app t_v all_args
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         (FStar_Syntax_Unionfind.change
                            uv.FStar_Syntax_Syntax.ctx_uvar_head sol;
                          ((t1, v1, all_args), wl1))))
           | uu____4359 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4379 =
          let uu____4392 =
            let uu____4393 = FStar_Syntax_Subst.compress k  in
            uu____4393.FStar_Syntax_Syntax.n  in
          match uu____4392 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____4446 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____4446)
              else
                (let uu____4460 = FStar_Syntax_Util.abs_formals t  in
                 match uu____4460 with
                 | (ys',t1,uu____4483) ->
                     let uu____4488 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4488))
          | uu____4529 ->
              let uu____4530 =
                let uu____4541 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4541)  in
              ((ys, t), uu____4530)
           in
        match uu____4379 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (FStar_Pervasives_Native.Some
                   (FStar_Syntax_Util.mk_residual_comp
                      FStar_Parser_Const.effect_Tot_lid
                      FStar_Pervasives_Native.None []))
            else
              (let c1 =
                 let uu____4590 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____4590 c  in
               FStar_Syntax_Util.abs ys1 t1
                 (FStar_Pervasives_Native.Some
                    (FStar_Syntax_Util.residual_comp_of_comp c1)))
  
let (solve_prob' :
  Prims.bool ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option ->
        uvi Prims.list -> worklist -> worklist)
  =
  fun resolve_ok  ->
    fun prob  ->
      fun logical_guard  ->
        fun uvis  ->
          fun wl  ->
            def_check_prob "solve_prob'" prob;
            (let phi =
               match logical_guard with
               | FStar_Pervasives_Native.None  -> FStar_Syntax_Util.t_true
               | FStar_Pervasives_Native.Some phi -> phi  in
             let assign_solution xs uv phi1 =
               (let uu____4664 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____4664
                then
                  let uu____4665 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____4666 = print_ctx_uvar uv  in
                  let uu____4667 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____4665 uu____4666 uu____4667
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                def_check_closed (p_loc prob) "solve_prob'" phi2;
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uu____4673 = p_guard_uvar prob  in
             match uu____4673 with
             | (xs,uv) ->
                 let fail1 uu____4685 =
                   let uu____4686 =
                     let uu____4687 =
                       FStar_Syntax_Print.ctx_uvar_to_string uv  in
                     let uu____4688 =
                       FStar_Syntax_Print.term_to_string (p_guard prob)  in
                     FStar_Util.format2
                       "Impossible: this instance %s has already been assigned a solution\n%s\n"
                       uu____4687 uu____4688
                      in
                   failwith uu____4686  in
                 let args_as_binders args =
                   FStar_All.pipe_right args
                     (FStar_List.collect
                        (fun uu____4738  ->
                           match uu____4738 with
                           | (a,i) ->
                               let uu____4751 =
                                 let uu____4752 =
                                   FStar_Syntax_Subst.compress a  in
                                 uu____4752.FStar_Syntax_Syntax.n  in
                               (match uu____4751 with
                                | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                                | uu____4770 -> (fail1 (); []))))
                    in
                 let wl1 =
                   let g = whnf wl.tcenv (p_guard prob)  in
                   let uu____4778 =
                     let uu____4779 = is_flex g  in
                     Prims.op_Negation uu____4779  in
                   if uu____4778
                   then (if resolve_ok then wl else (fail1 (); wl))
                   else
                     (let uu____4783 = destruct_flex_t g wl  in
                      match uu____4783 with
                      | ((uu____4788,uv1,args),wl1) ->
                          ((let uu____4793 = args_as_binders args  in
                            assign_solution uu____4793 uv1 phi);
                           wl1))
                    in
                 (commit uvis;
                  (let uu___167_4795 = wl1  in
                   {
                     attempting = (uu___167_4795.attempting);
                     wl_deferred = (uu___167_4795.wl_deferred);
                     ctr = (wl1.ctr + (Prims.parse_int "1"));
                     defer_ok = (uu___167_4795.defer_ok);
                     smt_ok = (uu___167_4795.smt_ok);
                     tcenv = (uu___167_4795.tcenv);
                     wl_implicits = (uu___167_4795.wl_implicits)
                   })))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____4816 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____4816
         then
           let uu____4817 = FStar_Util.string_of_int pid  in
           let uu____4818 =
             let uu____4819 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____4819 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____4817 uu____4818
         else ());
        commit sol;
        (let uu___168_4826 = wl  in
         {
           attempting = (uu___168_4826.attempting);
           wl_deferred = (uu___168_4826.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___168_4826.defer_ok);
           smt_ok = (uu___168_4826.smt_ok);
           tcenv = (uu___168_4826.tcenv);
           wl_implicits = (uu___168_4826.wl_implicits)
         })
  
let (solve_prob :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      uvi Prims.list -> worklist -> worklist)
  =
  fun prob  ->
    fun logical_guard  ->
      fun uvis  ->
        fun wl  ->
          def_check_prob "solve_prob.prob" prob;
          FStar_Util.iter_opt logical_guard
            (def_check_scoped "solve_prob.guard" prob);
          (let conj_guard1 t g =
             match (t, g) with
             | (uu____4888,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____4914 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____4914
              in
           (let uu____4920 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____4920
            then
              let uu____4921 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____4922 =
                let uu____4923 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____4923 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____4921 uu____4922
            else ());
           solve_prob' false prob logical_guard uvis wl)
  
let (occurs :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list,Prims.bool)
        FStar_Pervasives_Native.tuple2)
  =
  fun uk  ->
    fun t  ->
      let uvars1 =
        let uu____4948 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____4948 FStar_Util.set_elements  in
      let occurs =
        FStar_All.pipe_right uvars1
          (FStar_Util.for_some
             (fun uv  ->
                FStar_Syntax_Unionfind.equiv
                  uv.FStar_Syntax_Syntax.ctx_uvar_head
                  uk.FStar_Syntax_Syntax.ctx_uvar_head))
         in
      (uvars1, occurs)
  
let (occurs_check :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list,Prims.bool,Prims.string
                                                            FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3)
  =
  fun uk  ->
    fun t  ->
      let uu____4982 = occurs uk t  in
      match uu____4982 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5011 =
                 let uu____5012 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5013 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5012 uu____5013
                  in
               FStar_Pervasives_Native.Some uu____5011)
             in
          (uvars1, (Prims.op_Negation occurs1), msg)
  
let rec (maximal_prefix :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders,(FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.binders)
                                     FStar_Pervasives_Native.tuple2)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun bs'  ->
      match (bs, bs') with
      | ((b,i)::bs_tail,(b',i')::bs'_tail) ->
          if FStar_Syntax_Syntax.bv_eq b b'
          then
            let uu____5102 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5102 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5146 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____5194  ->
             match uu____5194 with
             | (x,uu____5204) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____5217 = FStar_List.last bs  in
      match uu____5217 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____5235) ->
          let uu____5240 =
            FStar_Util.prefix_until
              (fun uu___140_5255  ->
                 match uu___140_5255 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____5257 -> false) g
             in
          (match uu____5240 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____5270,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____5306 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____5306 with
        | (pfx,uu____5316) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____5328 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____5328 with
             | (uu____5335,src',wl1) ->
                 (FStar_Syntax_Unionfind.change
                    src.FStar_Syntax_Syntax.ctx_uvar_head src';
                  wl1))
  
let (restrict_all_uvars :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar Prims.list -> worklist -> worklist)
  =
  fun tgt  ->
    fun sources  ->
      fun wl  -> FStar_List.fold_right (restrict_ctx tgt) sources wl
  
let (intersect_binders :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun v1  ->
    fun v2  ->
      let as_set1 v3 =
        FStar_All.pipe_right v3
          (FStar_List.fold_left
             (fun out  ->
                fun x  ->
                  FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)
             FStar_Syntax_Syntax.no_names)
         in
      let v1_set = as_set1 v1  in
      let uu____5415 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____5469  ->
                fun uu____5470  ->
                  match (uu____5469, uu____5470) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____5551 =
                        let uu____5552 = FStar_Util.set_mem x v1_set  in
                        FStar_All.pipe_left Prims.op_Negation uu____5552  in
                      if uu____5551
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort
                            in
                         let uu____5577 =
                           FStar_Util.set_is_subset_of fvs isect_set  in
                         if uu____5577
                         then
                           let uu____5590 = FStar_Util.set_add x isect_set
                              in
                           (((x, imp) :: isect), uu____5590)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names))
         in
      match uu____5415 with | (isect,uu____5627) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____5656 'Auu____5657 .
    (FStar_Syntax_Syntax.bv,'Auu____5656) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____5657) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____5714  ->
              fun uu____5715  ->
                match (uu____5714, uu____5715) with
                | ((a,uu____5733),(b,uu____5735)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____5750 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____5750) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____5780  ->
           match uu____5780 with
           | (y,uu____5786) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____5797 'Auu____5798 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____5797) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____5798)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ctx  ->
      fun args  ->
        let rec aux seen args1 =
          match args1 with
          | [] -> FStar_Pervasives_Native.Some (FStar_List.rev seen)
          | arg::args2 ->
              let hd1 = norm_arg env arg  in
              (match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n
               with
               | FStar_Syntax_Syntax.Tm_name a ->
                   let uu____5907 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____5907
                   then FStar_Pervasives_Native.None
                   else
                     (let uu____5915 =
                        let uu____5918 = FStar_Syntax_Syntax.mk_binder a  in
                        uu____5918 :: seen  in
                      aux uu____5915 args2)
               | uu____5919 -> FStar_Pervasives_Native.None)
           in
        aux [] args
  
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | HeadMatch 
  | FullMatch [@@deriving show]
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____5949 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____5986 -> false
  
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____5992 -> false
  
let string_of_option :
  'Auu____5999 .
    ('Auu____5999 -> Prims.string) ->
      'Auu____5999 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___141_6014  ->
      match uu___141_6014 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____6020 = f x  in Prims.strcat "Some " uu____6020
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___142_6025  ->
    match uu___142_6025 with
    | MisMatch (d1,d2) ->
        let uu____6036 =
          let uu____6037 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____6038 =
            let uu____6039 =
              let uu____6040 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____6040 ")"  in
            Prims.strcat ") (" uu____6039  in
          Prims.strcat uu____6037 uu____6038  in
        Prims.strcat "MisMatch (" uu____6036
    | HeadMatch  -> "HeadMatch"
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___143_6045  ->
    match uu___143_6045 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____6060 -> HeadMatch
  
let (and_match : match_result -> (unit -> match_result) -> match_result) =
  fun m1  ->
    fun m2  ->
      match m1 with
      | MisMatch (i,j) -> MisMatch (i, j)
      | HeadMatch  ->
          let uu____6090 = m2 ()  in
          (match uu____6090 with
           | MisMatch (i,j) -> MisMatch (i, j)
           | uu____6105 -> HeadMatch)
      | FullMatch  -> m2 ()
  
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env  ->
    fun fv  ->
      match fv.FStar_Syntax_Syntax.fv_delta with
      | FStar_Syntax_Syntax.Delta_abstract d ->
          if
            ((env.FStar_TypeChecker_Env.curmodule).FStar_Ident.str =
               ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr)
              && (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface)
          then d
          else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when
          i > (Prims.parse_int "0") ->
          let uu____6119 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____6119 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____6130 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
  
let rec (delta_depth_of_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____6153 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____6162 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____6190 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____6190
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____6191 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____6192 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____6193 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____6200 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____6213 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____6237) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____6243,uu____6244) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____6286) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6307;
             FStar_Syntax_Syntax.index = uu____6308;
             FStar_Syntax_Syntax.sort = t2;_},uu____6310)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____6317 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____6318 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____6319 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____6332 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____6339 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____6357 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____6357
  
let rec (head_matches :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> match_result)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let t11 = FStar_Syntax_Util.unmeta t1  in
        let t21 = FStar_Syntax_Util.unmeta t2  in
        match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____6384 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____6384
            then FullMatch
            else
              (let uu____6386 =
                 let uu____6395 =
                   let uu____6398 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____6398  in
                 let uu____6399 =
                   let uu____6402 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____6402  in
                 (uu____6395, uu____6399)  in
               MisMatch uu____6386)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____6408),FStar_Syntax_Syntax.Tm_uinst (g,uu____6410)) ->
            let uu____6419 = head_matches env f g  in
            FStar_All.pipe_right uu____6419 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____6422 = FStar_Const.eq_const c d  in
            if uu____6422
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____6429),FStar_Syntax_Syntax.Tm_uvar (uv',uu____6431)) ->
            let uu____6440 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____6440
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____6447),FStar_Syntax_Syntax.Tm_refine (y,uu____6449)) ->
            let uu____6458 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6458 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____6460),uu____6461) ->
            let uu____6466 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____6466 head_match
        | (uu____6467,FStar_Syntax_Syntax.Tm_refine (x,uu____6469)) ->
            let uu____6474 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____6474 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____6475,FStar_Syntax_Syntax.Tm_type
           uu____6476) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____6477,FStar_Syntax_Syntax.Tm_arrow uu____6478) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6504),FStar_Syntax_Syntax.Tm_app (head',uu____6506))
            ->
            let uu____6547 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6547 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6549),uu____6550) ->
            let uu____6571 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6571 head_match
        | (uu____6572,FStar_Syntax_Syntax.Tm_app (head1,uu____6574)) ->
            let uu____6595 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6595 head_match
        | uu____6596 ->
            let uu____6601 =
              let uu____6610 = delta_depth_of_term env t11  in
              let uu____6613 = delta_depth_of_term env t21  in
              (uu____6610, uu____6613)  in
            MisMatch uu____6601
  
let head_matches_delta :
  'Auu____6630 .
    FStar_TypeChecker_Env.env ->
      'Auu____6630 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            (match_result,(FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
                            FStar_Pervasives_Native.tuple2
                            FStar_Pervasives_Native.option)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun wl  ->
      fun t1  ->
        fun t2  ->
          let maybe_inline t =
            let uu____6677 = FStar_Syntax_Util.head_and_args t  in
            match uu____6677 with
            | (head1,uu____6695) ->
                let uu____6716 =
                  let uu____6717 = FStar_Syntax_Util.un_uinst head1  in
                  uu____6717.FStar_Syntax_Syntax.n  in
                (match uu____6716 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____6723 =
                       let uu____6724 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          in
                       FStar_All.pipe_right uu____6724 FStar_Option.isSome
                        in
                     if uu____6723
                     then
                       let uu____6743 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t
                          in
                       FStar_All.pipe_right uu____6743
                         (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                     else FStar_Pervasives_Native.None
                 | uu____6747 -> FStar_Pervasives_Native.None)
             in
          let success d r t11 t21 =
            (r,
              (if d > (Prims.parse_int "0")
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let fail1 r = (r, FStar_Pervasives_Native.None)  in
          let rec aux retry n_delta t11 t21 =
            let r = head_matches env t11 t21  in
            let reduce_one_and_try_again d1 d2 =
              let d1_greater_than_d2 =
                FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
              let uu____6880 =
                if d1_greater_than_d2
                then
                  let t1' =
                    normalize_refinement
                      [FStar_TypeChecker_Normalize.UnfoldUntil d2;
                      FStar_TypeChecker_Normalize.Weak;
                      FStar_TypeChecker_Normalize.HNF] env wl t11
                     in
                  (t1', t21)
                else
                  (let t2' =
                     normalize_refinement
                       [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                       FStar_TypeChecker_Normalize.Weak;
                       FStar_TypeChecker_Normalize.HNF] env wl t21
                      in
                   (t11, t2'))
                 in
              match uu____6880 with
              | (t12,t22) ->
                  aux retry (n_delta + (Prims.parse_int "1")) t12 t22
               in
            let reduce_both_and_try_again d r1 =
              let uu____6925 = FStar_TypeChecker_Common.decr_delta_depth d
                 in
              match uu____6925 with
              | FStar_Pervasives_Native.None  -> fail1 r1
              | FStar_Pervasives_Native.Some d1 ->
                  let t12 =
                    normalize_refinement
                      [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                      FStar_TypeChecker_Normalize.Weak;
                      FStar_TypeChecker_Normalize.HNF] env wl t11
                     in
                  let t22 =
                    normalize_refinement
                      [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                      FStar_TypeChecker_Normalize.Weak;
                      FStar_TypeChecker_Normalize.HNF] env wl t21
                     in
                  aux retry (n_delta + (Prims.parse_int "1")) t12 t22
               in
            match r with
            | MisMatch
                (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational_at_level
                 i),FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational_at_level j))
                when
                ((i > (Prims.parse_int "1")) || (j > (Prims.parse_int "1")))
                  && (i <> j)
                ->
                reduce_one_and_try_again
                  (FStar_Syntax_Syntax.Delta_equational_at_level i)
                  (FStar_Syntax_Syntax.Delta_equational_at_level j)
            | MisMatch
                (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational_at_level
                 uu____6957),uu____6958)
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6976 =
                     let uu____6985 = maybe_inline t11  in
                     let uu____6988 = maybe_inline t21  in
                     (uu____6985, uu____6988)  in
                   match uu____6976 with
                   | (FStar_Pervasives_Native.None
                      ,FStar_Pervasives_Native.None ) -> fail1 r
                   | (FStar_Pervasives_Native.Some
                      t12,FStar_Pervasives_Native.None ) ->
                       aux false (n_delta + (Prims.parse_int "1")) t12 t21
                   | (FStar_Pervasives_Native.None
                      ,FStar_Pervasives_Native.Some t22) ->
                       aux false (n_delta + (Prims.parse_int "1")) t11 t22
                   | (FStar_Pervasives_Native.Some
                      t12,FStar_Pervasives_Native.Some t22) ->
                       aux false (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch
                (uu____7025,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational_at_level uu____7026))
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____7044 =
                     let uu____7053 = maybe_inline t11  in
                     let uu____7056 = maybe_inline t21  in
                     (uu____7053, uu____7056)  in
                   match uu____7044 with
                   | (FStar_Pervasives_Native.None
                      ,FStar_Pervasives_Native.None ) -> fail1 r
                   | (FStar_Pervasives_Native.Some
                      t12,FStar_Pervasives_Native.None ) ->
                       aux false (n_delta + (Prims.parse_int "1")) t12 t21
                   | (FStar_Pervasives_Native.None
                      ,FStar_Pervasives_Native.Some t22) ->
                       aux false (n_delta + (Prims.parse_int "1")) t11 t22
                   | (FStar_Pervasives_Native.Some
                      t12,FStar_Pervasives_Native.Some t22) ->
                       aux false (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch
                (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some
                 d2)
                when d1 = d2 -> reduce_both_and_try_again d1 r
            | MisMatch
                (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some
                 d2)
                -> reduce_one_and_try_again d1 d2
            | MisMatch uu____7105 -> fail1 r
            | uu____7114 -> success n_delta r t11 t21  in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____7127 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____7127
           then
             let uu____7128 = FStar_Syntax_Print.term_to_string t1  in
             let uu____7129 = FStar_Syntax_Print.term_to_string t2  in
             let uu____7130 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____7137 =
               if
                 (FStar_Pervasives_Native.snd r) =
                   FStar_Pervasives_Native.None
               then "None"
               else
                 (let uu____7155 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____7155
                    (fun uu____7189  ->
                       match uu____7189 with
                       | (t11,t21) ->
                           let uu____7196 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____7197 =
                             let uu____7198 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.strcat "; " uu____7198  in
                           Prims.strcat uu____7196 uu____7197))
                in
             FStar_Util.print4 "head_matches (%s, %s) = %s (%s)\n" uu____7128
               uu____7129 uu____7130 uu____7137
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____7210 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____7210 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___144_7223  ->
    match uu___144_7223 with
    | FStar_TypeChecker_Common.Rigid_rigid  -> (Prims.parse_int "0")
    | FStar_TypeChecker_Common.Flex_rigid_eq  -> (Prims.parse_int "1")
    | FStar_TypeChecker_Common.Flex_flex_pattern_eq  -> (Prims.parse_int "2")
    | FStar_TypeChecker_Common.Flex_rigid  -> (Prims.parse_int "3")
    | FStar_TypeChecker_Common.Rigid_flex  -> (Prims.parse_int "4")
    | FStar_TypeChecker_Common.Flex_flex  -> (Prims.parse_int "5")
  
let (rank_leq :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Common.rank_t -> Prims.bool)
  = fun r1  -> fun r2  -> (rank_t_num r1) <= (rank_t_num r2) 
let (rank_less_than :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Common.rank_t -> Prims.bool)
  = fun r1  -> fun r2  -> (r1 <> r2) && ((rank_t_num r1) <= (rank_t_num r2)) 
let (compress_tprob :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem ->
      FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem)
  =
  fun tcenv  ->
    fun p  ->
      let uu___169_7260 = p  in
      let uu____7263 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____7264 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___169_7260.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____7263;
        FStar_TypeChecker_Common.relation =
          (uu___169_7260.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____7264;
        FStar_TypeChecker_Common.element =
          (uu___169_7260.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___169_7260.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___169_7260.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___169_7260.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___169_7260.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___169_7260.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____7278 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____7278
            (fun _0_23  -> FStar_TypeChecker_Common.TProb _0_23)
      | FStar_TypeChecker_Common.CProb uu____7283 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____7305 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____7305 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____7313 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____7313 with
           | (lh,lhs_args) ->
               let uu____7354 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____7354 with
                | (rh,rhs_args) ->
                    let uu____7395 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7408,FStar_Syntax_Syntax.Tm_uvar uu____7409)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____7474 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7497,uu____7498)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____7507,FStar_Syntax_Syntax.Tm_uvar uu____7508)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7517,FStar_Syntax_Syntax.Tm_arrow uu____7518)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___170_7540 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_7540.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_7540.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_7540.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_7540.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_7540.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___170_7540.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_7540.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_7540.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_7540.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____7543,FStar_Syntax_Syntax.Tm_type uu____7544)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___170_7554 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_7554.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_7554.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_7554.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_7554.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_7554.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___170_7554.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_7554.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_7554.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_7554.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____7557,FStar_Syntax_Syntax.Tm_uvar uu____7558)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___170_7568 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_7568.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_7568.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_7568.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_7568.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_7568.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___170_7568.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_7568.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_7568.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_7568.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____7571,FStar_Syntax_Syntax.Tm_uvar uu____7572)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____7581,uu____7582)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____7591,FStar_Syntax_Syntax.Tm_uvar uu____7592)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____7601,uu____7602) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____7395 with
                     | (rank,tp1) ->
                         let uu____7615 =
                           FStar_All.pipe_right
                             (let uu___171_7619 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___171_7619.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___171_7619.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___171_7619.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___171_7619.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___171_7619.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___171_7619.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___171_7619.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___171_7619.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___171_7619.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_24  ->
                                FStar_TypeChecker_Common.TProb _0_24)
                            in
                         (rank, uu____7615))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____7625 =
            FStar_All.pipe_right
              (let uu___172_7629 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___172_7629.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___172_7629.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___172_7629.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___172_7629.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___172_7629.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___172_7629.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___172_7629.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___172_7629.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___172_7629.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_25  -> FStar_TypeChecker_Common.CProb _0_25)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____7625)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____7690 probs =
      match uu____7690 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____7771 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____7792 = rank wl.tcenv hd1  in
               (match uu____7792 with
                | (rank1,hd2) ->
                    if rank_leq rank1 FStar_TypeChecker_Common.Flex_rigid_eq
                    then
                      (match min1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.Some
                             (hd2, (FStar_List.append out tl1), rank1)
                       | FStar_Pervasives_Native.Some m ->
                           FStar_Pervasives_Native.Some
                             (hd2, (FStar_List.append out (m :: tl1)), rank1))
                    else
                      (let uu____7851 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____7855 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____7855)
                          in
                       if uu____7851
                       then
                         match min1 with
                         | FStar_Pervasives_Native.None  ->
                             aux
                               ((FStar_Pervasives_Native.Some rank1),
                                 (FStar_Pervasives_Native.Some hd2), out) tl1
                         | FStar_Pervasives_Native.Some m ->
                             aux
                               ((FStar_Pervasives_Native.Some rank1),
                                 (FStar_Pervasives_Native.Some hd2), (m ::
                                 out)) tl1
                       else aux (min_rank, min1, (hd2 :: out)) tl1)))
       in
    aux (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, [])
      wl.attempting
  
let (flex_prob_closing :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob -> Prims.bool)
  =
  fun tcenv  ->
    fun bs  ->
      fun p  ->
        let flex_will_be_closed t =
          let uu____7923 = FStar_Syntax_Util.head_and_args t  in
          match uu____7923 with
          | (hd1,uu____7939) ->
              let uu____7960 =
                let uu____7961 = FStar_Syntax_Subst.compress hd1  in
                uu____7961.FStar_Syntax_Syntax.n  in
              (match uu____7960 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____7965) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____7983  ->
                           match uu____7983 with
                           | (y,uu____7989) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____8003  ->
                                       match uu____8003 with
                                       | (x,uu____8009) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____8010 -> false)
           in
        let uu____8011 = rank tcenv p  in
        match uu____8011 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____8018 -> true
             | FStar_TypeChecker_Common.TProb p2 ->
                 (match r with
                  | FStar_TypeChecker_Common.Rigid_rigid  -> true
                  | FStar_TypeChecker_Common.Flex_rigid_eq  -> true
                  | FStar_TypeChecker_Common.Flex_flex_pattern_eq  -> true
                  | FStar_TypeChecker_Common.Flex_rigid  ->
                      flex_will_be_closed p2.FStar_TypeChecker_Common.lhs
                  | FStar_TypeChecker_Common.Rigid_flex  ->
                      flex_will_be_closed p2.FStar_TypeChecker_Common.rhs
                  | FStar_TypeChecker_Common.Flex_flex  ->
                      (p2.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ)
                        &&
                        ((flex_will_be_closed p2.FStar_TypeChecker_Common.lhs)
                           ||
                           (flex_will_be_closed
                              p2.FStar_TypeChecker_Common.rhs))))
  
type univ_eq_sol =
  | UDeferred of worklist 
  | USolved of worklist 
  | UFailed of Prims.string [@@deriving show]
let (uu___is_UDeferred : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____8045 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____8059 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____8073 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> Prims.string) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let rec (really_solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun pid_orig  ->
    fun wl  ->
      fun u1  ->
        fun u2  ->
          let u11 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1  in
          let u21 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2  in
          let rec occurs_univ v1 u =
            match u with
            | FStar_Syntax_Syntax.U_max us ->
                FStar_All.pipe_right us
                  (FStar_Util.for_some
                     (fun u3  ->
                        let uu____8125 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____8125 with
                        | (k,uu____8131) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____8141 -> false)))
            | uu____8142 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____8194 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____8200 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____8200 = (Prims.parse_int "0")))
                           in
                        if uu____8194 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____8216 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____8222 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____8222 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____8216)
               in
            let uu____8223 = filter1 u12  in
            let uu____8226 = filter1 u22  in (uu____8223, uu____8226)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____8255 = filter_out_common_univs us1 us2  in
                (match uu____8255 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____8314 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____8314 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____8317 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____8327 =
                          let uu____8328 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____8329 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____8328
                            uu____8329
                           in
                        UFailed uu____8327))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8353 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8353 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____8379 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____8379 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____8382 ->
                let uu____8387 =
                  let uu____8388 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____8389 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____8388
                    uu____8389 msg
                   in
                UFailed uu____8387
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____8390,uu____8391) ->
              let uu____8392 =
                let uu____8393 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8394 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8393 uu____8394
                 in
              failwith uu____8392
          | (FStar_Syntax_Syntax.U_unknown ,uu____8395) ->
              let uu____8396 =
                let uu____8397 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8398 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8397 uu____8398
                 in
              failwith uu____8396
          | (uu____8399,FStar_Syntax_Syntax.U_bvar uu____8400) ->
              let uu____8401 =
                let uu____8402 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8403 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8402 uu____8403
                 in
              failwith uu____8401
          | (uu____8404,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____8405 =
                let uu____8406 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____8407 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____8406 uu____8407
                 in
              failwith uu____8405
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____8431 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____8431
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____8445 = occurs_univ v1 u3  in
              if uu____8445
              then
                let uu____8446 =
                  let uu____8447 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8448 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8447 uu____8448
                   in
                try_umax_components u11 u21 uu____8446
              else
                (let uu____8450 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8450)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____8462 = occurs_univ v1 u3  in
              if uu____8462
              then
                let uu____8463 =
                  let uu____8464 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____8465 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____8464 uu____8465
                   in
                try_umax_components u11 u21 uu____8463
              else
                (let uu____8467 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____8467)
          | (FStar_Syntax_Syntax.U_max uu____8468,uu____8469) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8475 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8475
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____8477,FStar_Syntax_Syntax.U_max uu____8478) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____8484 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____8484
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____8486,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____8487,FStar_Syntax_Syntax.U_name
             uu____8488) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____8489) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____8490) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8491,FStar_Syntax_Syntax.U_succ
             uu____8492) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____8493,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
  
let (solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun orig  ->
    fun wl  ->
      fun u1  ->
        fun u2  ->
          if (wl.tcenv).FStar_TypeChecker_Env.lax_universes
          then USolved wl
          else really_solve_universe_eq orig wl u1 u2
  
let match_num_binders :
  'a 'b .
    ('a Prims.list,'a Prims.list -> 'b) FStar_Pervasives_Native.tuple2 ->
      ('a Prims.list,'a Prims.list -> 'b) FStar_Pervasives_Native.tuple2 ->
        (('a Prims.list,'b) FStar_Pervasives_Native.tuple2,('a Prims.list,
                                                             'b)
                                                             FStar_Pervasives_Native.tuple2)
          FStar_Pervasives_Native.tuple2
  =
  fun bc1  ->
    fun bc2  ->
      let uu____8593 = bc1  in
      match uu____8593 with
      | (bs1,mk_cod1) ->
          let uu____8637 = bc2  in
          (match uu____8637 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____8748 = aux xs ys  in
                     (match uu____8748 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____8831 =
                       let uu____8838 = mk_cod1 xs  in ([], uu____8838)  in
                     let uu____8841 =
                       let uu____8848 = mk_cod2 ys  in ([], uu____8848)  in
                     (uu____8831, uu____8841)
                  in
               aux bs1 bs2)
  
let is_flex_pat :
  'Auu____8871 'Auu____8872 'Auu____8873 .
    ('Auu____8871,'Auu____8872,'Auu____8873 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___145_8886  ->
    match uu___145_8886 with
    | (uu____8895,uu____8896,[]) -> true
    | uu____8899 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____8930 = f  in
      match uu____8930 with
      | (uu____8937,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____8938;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____8939;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____8942;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____8943;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____8944;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____8996  ->
                 match uu____8996 with
                 | (y,uu____9002) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____9124 =
                  let uu____9137 =
                    let uu____9140 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9140  in
                  ((FStar_List.rev pat_binders), uu____9137)  in
                FStar_Pervasives_Native.Some uu____9124
            | (uu____9167,[]) ->
                let uu____9190 =
                  let uu____9203 =
                    let uu____9206 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____9206  in
                  ((FStar_List.rev pat_binders), uu____9203)  in
                FStar_Pervasives_Native.Some uu____9190
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____9271 =
                  let uu____9272 = FStar_Syntax_Subst.compress a  in
                  uu____9272.FStar_Syntax_Syntax.n  in
                (match uu____9271 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____9290 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____9290
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___173_9311 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___173_9311.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___173_9311.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____9315 =
                            let uu____9316 =
                              let uu____9323 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____9323)  in
                            FStar_Syntax_Syntax.NT uu____9316  in
                          [uu____9315]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___174_9335 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___174_9335.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___174_9335.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____9336 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____9364 =
                  let uu____9377 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____9377  in
                (match uu____9364 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____9440 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____9467 ->
               let uu____9468 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____9468 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____9744 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____9744
       then
         let uu____9745 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____9745
       else ());
      (let uu____9747 = next_prob probs  in
       match uu____9747 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___175_9774 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___175_9774.wl_deferred);
               ctr = (uu___175_9774.ctr);
               defer_ok = (uu___175_9774.defer_ok);
               smt_ok = (uu___175_9774.smt_ok);
               tcenv = (uu___175_9774.tcenv);
               wl_implicits = (uu___175_9774.wl_implicits)
             }  in
           (match hd1 with
            | FStar_TypeChecker_Common.CProb cp ->
                solve_c env (maybe_invert cp) probs1
            | FStar_TypeChecker_Common.TProb tp ->
                let uu____9781 =
                  FStar_Util.physical_equality
                    tp.FStar_TypeChecker_Common.lhs
                    tp.FStar_TypeChecker_Common.rhs
                   in
                if uu____9781
                then
                  let uu____9782 =
                    solve_prob hd1 FStar_Pervasives_Native.None [] probs1  in
                  solve env uu____9782
                else
                  if
                    (rank1 = FStar_TypeChecker_Common.Rigid_rigid) ||
                      ((tp.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                         && (rank1 <> FStar_TypeChecker_Common.Flex_flex))
                  then solve_t' env tp probs1
                  else
                    if probs1.defer_ok
                    then
                      solve env
                        (defer "deferring flex_rigid or flex_flex subtyping"
                           hd1 probs1)
                    else
                      if rank1 = FStar_TypeChecker_Common.Flex_flex
                      then
                        solve_t' env
                          (let uu___176_9787 = tp  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___176_9787.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs =
                               (uu___176_9787.FStar_TypeChecker_Common.lhs);
                             FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.EQ;
                             FStar_TypeChecker_Common.rhs =
                               (uu___176_9787.FStar_TypeChecker_Common.rhs);
                             FStar_TypeChecker_Common.element =
                               (uu___176_9787.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___176_9787.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.logical_guard_uvar =
                               (uu___176_9787.FStar_TypeChecker_Common.logical_guard_uvar);
                             FStar_TypeChecker_Common.reason =
                               (uu___176_9787.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___176_9787.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___176_9787.FStar_TypeChecker_Common.rank)
                           }) probs1
                      else
                        solve_rigid_flex_or_flex_rigid_subtyping rank1 env tp
                          probs1)
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____9809 ->
                let uu____9818 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9877  ->
                          match uu____9877 with
                          | (c,uu____9885,uu____9886) -> c < probs.ctr))
                   in
                (match uu____9818 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9927 =
                            let uu____9932 =
                              FStar_List.map
                                (fun uu____9947  ->
                                   match uu____9947 with
                                   | (uu____9958,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____9932, (probs.wl_implicits))  in
                          Success uu____9927
                      | uu____9961 ->
                          let uu____9970 =
                            let uu___177_9971 = probs  in
                            let uu____9972 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9991  ->
                                      match uu____9991 with
                                      | (uu____9998,uu____9999,y) -> y))
                               in
                            {
                              attempting = uu____9972;
                              wl_deferred = rest;
                              ctr = (uu___177_9971.ctr);
                              defer_ok = (uu___177_9971.defer_ok);
                              smt_ok = (uu___177_9971.smt_ok);
                              tcenv = (uu___177_9971.tcenv);
                              wl_implicits = (uu___177_9971.wl_implicits)
                            }  in
                          solve env uu____9970))))

and (solve_one_universe_eq :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> worklist -> solution)
  =
  fun env  ->
    fun orig  ->
      fun u1  ->
        fun u2  ->
          fun wl  ->
            let uu____10006 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____10006 with
            | USolved wl1 ->
                let uu____10008 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____10008
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 -> solve env (defer "" orig wl1)

and (solve_maybe_uinsts :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> worklist -> univ_eq_sol)
  =
  fun env  ->
    fun orig  ->
      fun t1  ->
        fun t2  ->
          fun wl  ->
            let rec aux wl1 us1 us2 =
              match (us1, us2) with
              | ([],[]) -> USolved wl1
              | (u1::us11,u2::us21) ->
                  let uu____10060 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____10060 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____10063 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____10075;
                  FStar_Syntax_Syntax.vars = uu____10076;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____10079;
                  FStar_Syntax_Syntax.vars = uu____10080;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____10092,uu____10093) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____10100,FStar_Syntax_Syntax.Tm_uinst uu____10101) ->
                failwith "Impossible: expect head symbols to match"
            | uu____10108 -> USolved wl

and (giveup_or_defer :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> Prims.string -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun msg  ->
          if wl.defer_ok
          then
            ((let uu____10118 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10118
              then
                let uu____10119 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____10119 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig

and (solve_rigid_flex_or_flex_rigid_subtyping :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Env.env -> tprob -> worklist -> solution)
  =
  fun rank1  ->
    fun env  ->
      fun tp  ->
        fun wl  ->
          let flip = rank1 = FStar_TypeChecker_Common.Flex_rigid  in
          let meet_or_join op ts env1 wl1 =
            let eq_prob t1 t2 wl2 =
              let uu____10204 =
                new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                  FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                  "join/meet refinements"
                 in
              match uu____10204 with
              | (p,wl3) -> ((FStar_TypeChecker_Common.TProb p), wl3)  in
            let pairwise t1 t2 wl2 =
              (let uu____10256 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                   (FStar_Options.Other "Rel")
                  in
               if uu____10256
               then
                 let uu____10257 = FStar_Syntax_Print.term_to_string t1  in
                 let uu____10258 = FStar_Syntax_Print.term_to_string t2  in
                 FStar_Util.print2 "pairwise: %s and %s" uu____10257
                   uu____10258
               else ());
              (let uu____10260 = head_matches_delta env1 () t1 t2  in
               match uu____10260 with
               | (mr,ts1) ->
                   (match mr with
                    | MisMatch uu____10305 ->
                        let uu____10314 = eq_prob t1 t2 wl2  in
                        (match uu____10314 with | (p,wl3) -> (t1, [p], wl3))
                    | FullMatch  ->
                        (match ts1 with
                         | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             (t11, [], wl2))
                    | HeadMatch  ->
                        let uu____10361 =
                          match ts1 with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____10376 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____10377 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____10376, uu____10377)
                          | FStar_Pervasives_Native.None  ->
                              let uu____10382 =
                                FStar_Syntax_Subst.compress t1  in
                              let uu____10383 =
                                FStar_Syntax_Subst.compress t2  in
                              (uu____10382, uu____10383)
                           in
                        (match uu____10361 with
                         | (t11,t21) ->
                             let try_eq t12 t22 wl3 =
                               let uu____10414 =
                                 FStar_Syntax_Util.head_and_args t12  in
                               match uu____10414 with
                               | (t1_hd,t1_args) ->
                                   let uu____10453 =
                                     FStar_Syntax_Util.head_and_args t22  in
                                   (match uu____10453 with
                                    | (t2_hd,t2_args) ->
                                        if
                                          (FStar_List.length t1_args) <>
                                            (FStar_List.length t2_args)
                                        then FStar_Pervasives_Native.None
                                        else
                                          (let uu____10507 =
                                             let uu____10514 =
                                               let uu____10523 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t1_hd
                                                  in
                                               uu____10523 :: t1_args  in
                                             let uu____10536 =
                                               let uu____10543 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t2_hd
                                                  in
                                               uu____10543 :: t2_args  in
                                             FStar_List.fold_left2
                                               (fun uu____10584  ->
                                                  fun uu____10585  ->
                                                    fun uu____10586  ->
                                                      match (uu____10584,
                                                              uu____10585,
                                                              uu____10586)
                                                      with
                                                      | ((probs,wl4),
                                                         (a1,uu____10628),
                                                         (a2,uu____10630)) ->
                                                          let uu____10655 =
                                                            eq_prob a1 a2 wl4
                                                             in
                                                          (match uu____10655
                                                           with
                                                           | (p,wl5) ->
                                                               ((p :: probs),
                                                                 wl5)))
                                               ([], wl3) uu____10514
                                               uu____10536
                                              in
                                           match uu____10507 with
                                           | (probs,wl4) ->
                                               let wl' =
                                                 let uu___178_10681 = wl4  in
                                                 {
                                                   attempting = probs;
                                                   wl_deferred = [];
                                                   ctr = (uu___178_10681.ctr);
                                                   defer_ok = false;
                                                   smt_ok = false;
                                                   tcenv =
                                                     (uu___178_10681.tcenv);
                                                   wl_implicits = []
                                                 }  in
                                               let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____10699 =
                                                 solve env1 wl'  in
                                               (match uu____10699 with
                                                | Success (uu____10702,imps)
                                                    ->
                                                    (FStar_Syntax_Unionfind.commit
                                                       tx;
                                                     FStar_Pervasives_Native.Some
                                                       ((let uu___179_10706 =
                                                           wl4  in
                                                         {
                                                           attempting =
                                                             (uu___179_10706.attempting);
                                                           wl_deferred =
                                                             (uu___179_10706.wl_deferred);
                                                           ctr =
                                                             (uu___179_10706.ctr);
                                                           defer_ok =
                                                             (uu___179_10706.defer_ok);
                                                           smt_ok =
                                                             (uu___179_10706.smt_ok);
                                                           tcenv =
                                                             (uu___179_10706.tcenv);
                                                           wl_implicits =
                                                             (FStar_List.append
                                                                wl4.wl_implicits
                                                                imps)
                                                         })))
                                                | Failed uu____10717 ->
                                                    (FStar_Syntax_Unionfind.rollback
                                                       tx;
                                                     FStar_Pervasives_Native.None))))
                                in
                             let combine t12 t22 wl3 =
                               let uu____10749 =
                                 base_and_refinement_maybe_delta false env1
                                   t12
                                  in
                               match uu____10749 with
                               | (t1_base,p1_opt) ->
                                   let uu____10790 =
                                     base_and_refinement_maybe_delta false
                                       env1 t22
                                      in
                                   (match uu____10790 with
                                    | (t2_base,p2_opt) ->
                                        let combine_refinements t_base
                                          p1_opt1 p2_opt1 =
                                          match (p1_opt1, p2_opt1) with
                                          | (FStar_Pervasives_Native.Some
                                             (x,phi1),FStar_Pervasives_Native.Some
                                             (y,phi2)) ->
                                              let x1 =
                                                FStar_Syntax_Syntax.freshen_bv
                                                  x
                                                 in
                                              let subst1 =
                                                [FStar_Syntax_Syntax.DB
                                                   ((Prims.parse_int "0"),
                                                     x1)]
                                                 in
                                              let phi11 =
                                                FStar_Syntax_Subst.subst
                                                  subst1 phi1
                                                 in
                                              let phi21 =
                                                FStar_Syntax_Subst.subst
                                                  subst1 phi2
                                                 in
                                              let uu____10921 =
                                                op phi11 phi21  in
                                              FStar_Syntax_Util.refine x1
                                                uu____10921
                                          | (FStar_Pervasives_Native.None
                                             ,FStar_Pervasives_Native.Some
                                             (x,phi)) ->
                                              let x1 =
                                                FStar_Syntax_Syntax.freshen_bv
                                                  x
                                                 in
                                              let subst1 =
                                                [FStar_Syntax_Syntax.DB
                                                   ((Prims.parse_int "0"),
                                                     x1)]
                                                 in
                                              let phi1 =
                                                FStar_Syntax_Subst.subst
                                                  subst1 phi
                                                 in
                                              let uu____10951 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              FStar_Syntax_Util.refine x1
                                                uu____10951
                                          | (FStar_Pervasives_Native.Some
                                             (x,phi),FStar_Pervasives_Native.None
                                             ) ->
                                              let x1 =
                                                FStar_Syntax_Syntax.freshen_bv
                                                  x
                                                 in
                                              let subst1 =
                                                [FStar_Syntax_Syntax.DB
                                                   ((Prims.parse_int "0"),
                                                     x1)]
                                                 in
                                              let phi1 =
                                                FStar_Syntax_Subst.subst
                                                  subst1 phi
                                                 in
                                              let uu____10981 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              FStar_Syntax_Util.refine x1
                                                uu____10981
                                          | uu____10984 -> t_base  in
                                        let uu____11001 =
                                          try_eq t1_base t2_base wl3  in
                                        (match uu____11001 with
                                         | FStar_Pervasives_Native.Some wl4
                                             ->
                                             let uu____11015 =
                                               combine_refinements t1_base
                                                 p1_opt p2_opt
                                                in
                                             (uu____11015, [], wl4)
                                         | FStar_Pervasives_Native.None  ->
                                             let uu____11022 =
                                               base_and_refinement_maybe_delta
                                                 true env1 t12
                                                in
                                             (match uu____11022 with
                                              | (t1_base1,p1_opt1) ->
                                                  let uu____11063 =
                                                    base_and_refinement_maybe_delta
                                                      true env1 t22
                                                     in
                                                  (match uu____11063 with
                                                   | (t2_base1,p2_opt1) ->
                                                       let uu____11104 =
                                                         eq_prob t1_base1
                                                           t2_base1 wl3
                                                          in
                                                       (match uu____11104
                                                        with
                                                        | (p,wl4) ->
                                                            let t =
                                                              combine_refinements
                                                                t1_base1
                                                                p1_opt1
                                                                p2_opt1
                                                               in
                                                            (t, [p], wl4))))))
                                in
                             let uu____11128 = combine t11 t21 wl2  in
                             (match uu____11128 with
                              | (t12,ps,wl3) ->
                                  ((let uu____11161 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env1)
                                        (FStar_Options.Other "Rel")
                                       in
                                    if uu____11161
                                    then
                                      let uu____11162 =
                                        FStar_Syntax_Print.term_to_string t12
                                         in
                                      FStar_Util.print1
                                        "pairwise fallback2 succeeded: %s"
                                        uu____11162
                                    else ());
                                   (t12, ps, wl3))))))
               in
            let rec aux uu____11201 ts1 =
              match uu____11201 with
              | (out,probs,wl2) ->
                  (match ts1 with
                   | [] -> (out, probs, wl2)
                   | t::ts2 ->
                       let uu____11264 = pairwise out t wl2  in
                       (match uu____11264 with
                        | (out1,probs',wl3) ->
                            aux (out1, (FStar_List.append probs probs'), wl3)
                              ts2))
               in
            let uu____11300 =
              let uu____11311 = FStar_List.hd ts  in (uu____11311, [], wl1)
               in
            let uu____11320 = FStar_List.tl ts  in
            aux uu____11300 uu____11320  in
          let uu____11327 =
            if flip
            then
              ((tp.FStar_TypeChecker_Common.lhs),
                (tp.FStar_TypeChecker_Common.rhs))
            else
              ((tp.FStar_TypeChecker_Common.rhs),
                (tp.FStar_TypeChecker_Common.lhs))
             in
          match uu____11327 with
          | (this_flex,this_rigid) ->
              let uu____11339 =
                let uu____11340 = FStar_Syntax_Subst.compress this_rigid  in
                uu____11340.FStar_Syntax_Syntax.n  in
              (match uu____11339 with
               | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                   let uu____11361 =
                     FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                   if uu____11361
                   then
                     let uu____11362 = destruct_flex_t this_flex wl  in
                     (match uu____11362 with
                      | (flex,wl1) ->
                          let uu____11369 = quasi_pattern env flex  in
                          (match uu____11369 with
                           | FStar_Pervasives_Native.None  ->
                               giveup env
                                 "flex-arrow subtyping, not a quasi pattern"
                                 (FStar_TypeChecker_Common.TProb tp)
                           | FStar_Pervasives_Native.Some (flex_bs,flex_t) ->
                               ((let uu____11387 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____11387
                                 then
                                   let uu____11388 =
                                     FStar_Util.string_of_int
                                       tp.FStar_TypeChecker_Common.pid
                                      in
                                   FStar_Util.print1
                                     "Trying to solve by imitating arrow:%s\n"
                                     uu____11388
                                 else ());
                                imitate_arrow
                                  (FStar_TypeChecker_Common.TProb tp) env wl1
                                  flex flex_bs flex_t
                                  tp.FStar_TypeChecker_Common.relation
                                  this_rigid)))
                   else
                     solve env
                       (attempt
                          [FStar_TypeChecker_Common.TProb
                             ((let uu___180_11393 = tp  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___180_11393.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___180_11393.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___180_11393.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___180_11393.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___180_11393.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___180_11393.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___180_11393.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___180_11393.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___180_11393.FStar_TypeChecker_Common.rank)
                               }))] wl)
               | uu____11394 ->
                   ((let uu____11396 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____11396
                     then
                       let uu____11397 =
                         FStar_Util.string_of_int
                           tp.FStar_TypeChecker_Common.pid
                          in
                       FStar_Util.print1
                         "Trying to solve by meeting refinements:%s\n"
                         uu____11397
                     else ());
                    (let uu____11399 =
                       FStar_Syntax_Util.head_and_args this_flex  in
                     match uu____11399 with
                     | (u,_args) ->
                         let uu____11436 =
                           let uu____11437 = FStar_Syntax_Subst.compress u
                              in
                           uu____11437.FStar_Syntax_Syntax.n  in
                         (match uu____11436 with
                          | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                              let equiv1 t =
                                let uu____11452 =
                                  FStar_Syntax_Util.head_and_args t  in
                                match uu____11452 with
                                | (u',uu____11468) ->
                                    let uu____11489 =
                                      let uu____11490 = whnf env u'  in
                                      uu____11490.FStar_Syntax_Syntax.n  in
                                    (match uu____11489 with
                                     | FStar_Syntax_Syntax.Tm_uvar
                                         (ctx_uvar',_subst') ->
                                         FStar_Syntax_Unionfind.equiv
                                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                           ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                     | uu____11499 -> false)
                                 in
                              let uu____11500 =
                                FStar_All.pipe_right wl.attempting
                                  (FStar_List.partition
                                     (fun uu___146_11523  ->
                                        match uu___146_11523 with
                                        | FStar_TypeChecker_Common.TProb tp1
                                            ->
                                            let tp2 = maybe_invert tp1  in
                                            (match tp2.FStar_TypeChecker_Common.rank
                                             with
                                             | FStar_Pervasives_Native.Some
                                                 rank' when rank1 = rank' ->
                                                 if flip
                                                 then
                                                   equiv1
                                                     tp2.FStar_TypeChecker_Common.lhs
                                                 else
                                                   equiv1
                                                     tp2.FStar_TypeChecker_Common.rhs
                                             | uu____11532 -> false)
                                        | uu____11535 -> false))
                                 in
                              (match uu____11500 with
                               | (bounds_probs,rest) ->
                                   let bounds_typs =
                                     let uu____11549 = whnf env this_rigid
                                        in
                                     let uu____11550 =
                                       FStar_List.collect
                                         (fun uu___147_11556  ->
                                            match uu___147_11556 with
                                            | FStar_TypeChecker_Common.TProb
                                                p ->
                                                let uu____11562 =
                                                  if flip
                                                  then
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                  else
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                   in
                                                [uu____11562]
                                            | uu____11564 -> []) bounds_probs
                                        in
                                     uu____11549 :: uu____11550  in
                                   let uu____11565 =
                                     meet_or_join
                                       (if flip
                                        then FStar_Syntax_Util.mk_conj
                                        else FStar_Syntax_Util.mk_disj)
                                       bounds_typs env wl
                                      in
                                   (match uu____11565 with
                                    | (bound,sub_probs,wl1) ->
                                        let uu____11596 =
                                          let flex_u =
                                            flex_uvar_head this_flex  in
                                          let bound1 =
                                            let uu____11611 =
                                              let uu____11612 =
                                                FStar_Syntax_Subst.compress
                                                  bound
                                                 in
                                              uu____11612.FStar_Syntax_Syntax.n
                                               in
                                            match uu____11611 with
                                            | FStar_Syntax_Syntax.Tm_refine
                                                (x,phi) when
                                                (tp.FStar_TypeChecker_Common.relation
                                                   =
                                                   FStar_TypeChecker_Common.SUB)
                                                  &&
                                                  (let uu____11624 =
                                                     occurs flex_u
                                                       x.FStar_Syntax_Syntax.sort
                                                      in
                                                   FStar_Pervasives_Native.snd
                                                     uu____11624)
                                                -> x.FStar_Syntax_Syntax.sort
                                            | uu____11633 -> bound  in
                                          let uu____11634 =
                                            new_problem wl1 env bound1
                                              FStar_TypeChecker_Common.EQ
                                              this_flex
                                              FStar_Pervasives_Native.None
                                              tp.FStar_TypeChecker_Common.loc
                                              (if flip
                                               then "joining refinements"
                                               else "meeting refinements")
                                             in
                                          (bound1, uu____11634)  in
                                        (match uu____11596 with
                                         | (bound_typ,(eq_prob,wl2)) ->
                                             ((let uu____11662 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____11662
                                               then
                                                 let wl' =
                                                   let uu___181_11664 = wl2
                                                      in
                                                   {
                                                     attempting =
                                                       ((FStar_TypeChecker_Common.TProb
                                                           eq_prob) ::
                                                       sub_probs);
                                                     wl_deferred =
                                                       (uu___181_11664.wl_deferred);
                                                     ctr =
                                                       (uu___181_11664.ctr);
                                                     defer_ok =
                                                       (uu___181_11664.defer_ok);
                                                     smt_ok =
                                                       (uu___181_11664.smt_ok);
                                                     tcenv =
                                                       (uu___181_11664.tcenv);
                                                     wl_implicits =
                                                       (uu___181_11664.wl_implicits)
                                                   }  in
                                                 let uu____11665 =
                                                   wl_to_string wl'  in
                                                 FStar_Util.print1
                                                   "After meet/join refinements: %s\n"
                                                   uu____11665
                                               else ());
                                              (let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____11668 =
                                                 solve_t env eq_prob
                                                   (let uu___182_11670 = wl2
                                                       in
                                                    {
                                                      attempting = sub_probs;
                                                      wl_deferred =
                                                        (uu___182_11670.wl_deferred);
                                                      ctr =
                                                        (uu___182_11670.ctr);
                                                      defer_ok = false;
                                                      smt_ok =
                                                        (uu___182_11670.smt_ok);
                                                      tcenv =
                                                        (uu___182_11670.tcenv);
                                                      wl_implicits =
                                                        (uu___182_11670.wl_implicits)
                                                    })
                                                  in
                                               match uu____11668 with
                                               | Success uu____11671 ->
                                                   let wl3 =
                                                     let uu___183_11677 = wl2
                                                        in
                                                     {
                                                       attempting = rest;
                                                       wl_deferred =
                                                         (uu___183_11677.wl_deferred);
                                                       ctr =
                                                         (uu___183_11677.ctr);
                                                       defer_ok =
                                                         (uu___183_11677.defer_ok);
                                                       smt_ok =
                                                         (uu___183_11677.smt_ok);
                                                       tcenv =
                                                         (uu___183_11677.tcenv);
                                                       wl_implicits =
                                                         (uu___183_11677.wl_implicits)
                                                     }  in
                                                   let wl4 =
                                                     solve_prob' false
                                                       (FStar_TypeChecker_Common.TProb
                                                          tp)
                                                       FStar_Pervasives_Native.None
                                                       [] wl3
                                                      in
                                                   let uu____11681 =
                                                     FStar_List.fold_left
                                                       (fun wl5  ->
                                                          fun p  ->
                                                            solve_prob' true
                                                              p
                                                              FStar_Pervasives_Native.None
                                                              [] wl5) wl4
                                                       bounds_probs
                                                      in
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    solve env wl4)
                                               | Failed (p,msg) ->
                                                   (FStar_Syntax_Unionfind.rollback
                                                      tx;
                                                    (let uu____11693 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env)
                                                         (FStar_Options.Other
                                                            "Rel")
                                                        in
                                                     if uu____11693
                                                     then
                                                       let uu____11694 =
                                                         let uu____11695 =
                                                           FStar_List.map
                                                             (prob_to_string
                                                                env)
                                                             ((FStar_TypeChecker_Common.TProb
                                                                 eq_prob) ::
                                                             sub_probs)
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____11695
                                                           (FStar_String.concat
                                                              "\n")
                                                          in
                                                       FStar_Util.print1
                                                         "meet/join attempted and failed to solve problems:\n%s\n"
                                                         uu____11694
                                                     else ());
                                                    (let uu____11701 =
                                                       let uu____11716 =
                                                         base_and_refinement
                                                           env bound_typ
                                                          in
                                                       (rank1, uu____11716)
                                                        in
                                                     match uu____11701 with
                                                     | (FStar_TypeChecker_Common.Rigid_flex
                                                        ,(t_base,FStar_Pervasives_Native.Some
                                                          uu____11738))
                                                         ->
                                                         let uu____11763 =
                                                           new_problem wl2
                                                             env t_base
                                                             FStar_TypeChecker_Common.EQ
                                                             this_flex
                                                             FStar_Pervasives_Native.None
                                                             tp.FStar_TypeChecker_Common.loc
                                                             "widened subtyping"
                                                            in
                                                         (match uu____11763
                                                          with
                                                          | (eq_prob1,wl3) ->
                                                              let wl4 =
                                                                solve_prob'
                                                                  false
                                                                  (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                  (FStar_Pervasives_Native.Some
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1)))
                                                                  [] wl3
                                                                 in
                                                              solve env
                                                                (attempt
                                                                   [FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                   wl4))
                                                     | (FStar_TypeChecker_Common.Flex_rigid
                                                        ,(t_base,FStar_Pervasives_Native.Some
                                                          (x,phi)))
                                                         ->
                                                         let uu____11802 =
                                                           new_problem wl2
                                                             env t_base
                                                             FStar_TypeChecker_Common.EQ
                                                             this_flex
                                                             FStar_Pervasives_Native.None
                                                             tp.FStar_TypeChecker_Common.loc
                                                             "widened subtyping"
                                                            in
                                                         (match uu____11802
                                                          with
                                                          | (eq_prob1,wl3) ->
                                                              let phi1 =
                                                                guard_on_element
                                                                  wl3 tp x
                                                                  phi
                                                                 in
                                                              let wl4 =
                                                                let uu____11819
                                                                  =
                                                                  let uu____11824
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____11824
                                                                   in
                                                                solve_prob'
                                                                  false
                                                                  (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                  uu____11819
                                                                  [] wl3
                                                                 in
                                                              solve env
                                                                (attempt
                                                                   [FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                   wl4))
                                                     | uu____11829 ->
                                                         giveup env
                                                           (Prims.strcat
                                                              "failed to solve sub-problems: "
                                                              msg) p)))))))
                          | uu____11844 when flip ->
                              let uu____11845 =
                                let uu____11846 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format1
                                  "Impossible: Not a flex-rigid: %s"
                                  uu____11846
                                 in
                              failwith uu____11845
                          | uu____11847 ->
                              let uu____11848 =
                                let uu____11849 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format1
                                  "Impossible: Not a rigid-flex: %s"
                                  uu____11849
                                 in
                              failwith uu____11848))))

and (imitate_arrow :
  FStar_TypeChecker_Common.prob ->
    FStar_TypeChecker_Env.env ->
      worklist ->
        flex_t ->
          FStar_Syntax_Syntax.binders ->
            FStar_Syntax_Syntax.term ->
              FStar_TypeChecker_Common.rel ->
                FStar_Syntax_Syntax.term -> solution)
  =
  fun orig  ->
    fun env  ->
      fun wl  ->
        fun lhs  ->
          fun bs_lhs  ->
            fun t_res_lhs  ->
              fun rel  ->
                fun arrow1  ->
                  let bs_lhs_args =
                    FStar_List.map
                      (fun uu____11877  ->
                         match uu____11877 with
                         | (x,i) ->
                             let uu____11888 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____11888, i)) bs_lhs
                     in
                  let uu____11889 = lhs  in
                  match uu____11889 with
                  | (uu____11890,u_lhs,uu____11892) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____12005 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____12015 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____12015, univ)
                             in
                          match uu____12005 with
                          | (k,univ) ->
                              let uu____12028 =
                                let uu____12035 =
                                  let uu____12038 =
                                    FStar_Syntax_Syntax.mk_Total k  in
                                  FStar_Syntax_Util.arrow
                                    (FStar_List.append bs_lhs bs) uu____12038
                                   in
                                copy_uvar u_lhs uu____12035 wl2  in
                              (match uu____12028 with
                               | (uu____12051,u,wl3) ->
                                   let uu____12054 =
                                     let uu____12057 =
                                       FStar_Syntax_Syntax.mk_Tm_app u
                                         (FStar_List.append bs_lhs_args
                                            bs_terms)
                                         FStar_Pervasives_Native.None
                                         c.FStar_Syntax_Syntax.pos
                                        in
                                     f uu____12057
                                       (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____12054, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____12093 =
                              let uu____12106 =
                                let uu____12115 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____12115 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____12161  ->
                                   fun uu____12162  ->
                                     match (uu____12161, uu____12162) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____12253 =
                                           let uu____12260 =
                                             let uu____12263 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____12263
                                              in
                                           copy_uvar u_lhs uu____12260 wl2
                                            in
                                         (match uu____12253 with
                                          | (uu____12286,t_a,wl3) ->
                                              let uu____12289 =
                                                let uu____12296 =
                                                  let uu____12299 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      t_a
                                                     in
                                                  FStar_Syntax_Util.arrow bs
                                                    uu____12299
                                                   in
                                                copy_uvar u_lhs uu____12296
                                                  wl3
                                                 in
                                              (match uu____12289 with
                                               | (uu____12314,a',wl4) ->
                                                   let a'1 =
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       a' bs_terms
                                                       FStar_Pervasives_Native.None
                                                       a.FStar_Syntax_Syntax.pos
                                                      in
                                                   (((a'1, i) :: out_args),
                                                     wl4)))) uu____12106
                                ([], wl1)
                               in
                            (match uu____12093 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___184_12375 = ct  in
                                   let uu____12376 =
                                     let uu____12379 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____12379
                                      in
                                   let uu____12394 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___184_12375.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___184_12375.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____12376;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____12394;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___184_12375.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___185_12412 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___185_12412.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___185_12412.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____12415 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____12415 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____12469 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____12469 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____12486 =
                                          let uu____12491 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____12491)  in
                                        TERM uu____12486  in
                                      let uu____12492 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____12492 with
                                       | (sub_prob,wl3) ->
                                           let uu____12503 =
                                             let uu____12504 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____12504
                                              in
                                           solve env uu____12503))
                             | (x,imp)::formals2 ->
                                 let uu____12518 =
                                   let uu____12525 =
                                     let uu____12528 =
                                       let uu____12531 =
                                         let uu____12532 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____12532
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.mk_Total
                                         uu____12531
                                        in
                                     FStar_Syntax_Util.arrow
                                       (FStar_List.append bs_lhs bs)
                                       uu____12528
                                      in
                                   copy_uvar u_lhs uu____12525 wl1  in
                                 (match uu____12518 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let t_y =
                                        FStar_Syntax_Syntax.mk_Tm_app u_x
                                          (FStar_List.append bs_lhs_args
                                             bs_terms)
                                          FStar_Pervasives_Native.None
                                          (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                         in
                                      let y =
                                        let uu____12556 =
                                          let uu____12559 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____12559
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____12556 t_y
                                         in
                                      let uu____12560 =
                                        let uu____12563 =
                                          let uu____12566 =
                                            let uu____12567 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____12567, imp)  in
                                          [uu____12566]  in
                                        FStar_List.append bs_terms
                                          uu____12563
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____12560 formals2 wl2)
                              in
                           aux [] [] formals wl)

and (solve_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders ->
        FStar_TypeChecker_Common.prob ->
          worklist ->
            (worklist ->
               FStar_Syntax_Syntax.binders ->
                 FStar_TypeChecker_Env.env ->
                   FStar_Syntax_Syntax.subst_elt Prims.list ->
                     (FStar_TypeChecker_Common.prob,worklist)
                       FStar_Pervasives_Native.tuple2)
              -> solution)
  =
  fun env  ->
    fun bs1  ->
      fun bs2  ->
        fun orig  ->
          fun wl  ->
            fun rhs  ->
              (let uu____12609 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____12609
               then
                 let uu____12610 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____12611 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____12610 (rel_to_string (p_rel orig)) uu____12611
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____12716 = rhs wl1 scope env1 subst1  in
                     (match uu____12716 with
                      | (rhs_prob,wl2) ->
                          ((let uu____12736 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____12736
                            then
                              let uu____12737 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____12737
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___186_12791 = hd1  in
                       let uu____12792 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___186_12791.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___186_12791.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____12792
                       }  in
                     let hd21 =
                       let uu___187_12796 = hd2  in
                       let uu____12797 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___187_12796.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___187_12796.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____12797
                       }  in
                     let uu____12800 =
                       let uu____12805 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____12805
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____12800 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____12824 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____12824
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____12828 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____12828 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____12883 =
                                   close_forall env2 [(hd12, imp)] phi  in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____12883
                                  in
                               ((let uu____12895 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____12895
                                 then
                                   let uu____12896 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____12897 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____12896
                                     uu____12897
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____12924 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____12953 = aux wl [] env [] bs1 bs2  in
               match uu____12953 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   solve env (attempt sub_probs wl2))

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____13004 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____13004 wl)

and (solve_t_flex_rigid_eq :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      worklist -> flex_t -> FStar_Syntax_Syntax.term -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun lhs  ->
          fun rhs  ->
            let binders_as_bv_set bs =
              let uu____13018 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____13018 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____13048 = lhs1  in
              match uu____13048 with
              | (uu____13051,ctx_u,uu____13053) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____13059 ->
                        let uu____13060 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____13060 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____13107 = quasi_pattern env1 lhs1  in
              match uu____13107 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____13137) ->
                  let uu____13142 = lhs1  in
                  (match uu____13142 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____13156 = occurs_check ctx_u rhs1  in
                       (match uu____13156 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____13198 =
                                let uu____13205 =
                                  let uu____13206 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____13206
                                   in
                                FStar_Util.Inl uu____13205  in
                              (uu____13198, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____13226 =
                                 let uu____13227 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____13227  in
                               if uu____13226
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____13247 =
                                    let uu____13254 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____13254  in
                                  let uu____13259 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____13247, uu____13259)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____13321  ->
                     match uu____13321 with
                     | (x,i) ->
                         let uu____13332 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____13332, i)) bs_lhs
                 in
              let uu____13333 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____13333 with
              | (rhs_hd,args) ->
                  let uu____13370 = FStar_Util.prefix args  in
                  (match uu____13370 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____13428 = lhs1  in
                       (match uu____13428 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____13432 =
                              let uu____13443 =
                                let uu____13450 =
                                  let uu____13453 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____13453
                                   in
                                copy_uvar u_lhs uu____13450 wl1  in
                              match uu____13443 with
                              | (uu____13474,t_last_arg,wl2) ->
                                  let uu____13477 =
                                    let uu____13484 =
                                      let uu____13487 =
                                        let uu____13494 =
                                          let uu____13501 =
                                            FStar_Syntax_Syntax.null_binder
                                              t_last_arg
                                             in
                                          [uu____13501]  in
                                        FStar_List.append bs_lhs uu____13494
                                         in
                                      let uu____13518 =
                                        FStar_Syntax_Syntax.mk_Total
                                          t_res_lhs
                                         in
                                      FStar_Syntax_Util.arrow uu____13487
                                        uu____13518
                                       in
                                    copy_uvar u_lhs uu____13484 wl2  in
                                  (match uu____13477 with
                                   | (uu____13531,u_lhs',wl3) ->
                                       let lhs' =
                                         FStar_Syntax_Syntax.mk_Tm_app u_lhs'
                                           bs_lhs_args
                                           FStar_Pervasives_Native.None
                                           t_lhs.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____13537 =
                                         let uu____13544 =
                                           let uu____13547 =
                                             FStar_Syntax_Syntax.mk_Total
                                               t_last_arg
                                              in
                                           FStar_Syntax_Util.arrow bs_lhs
                                             uu____13547
                                            in
                                         copy_uvar u_lhs uu____13544 wl3  in
                                       (match uu____13537 with
                                        | (uu____13560,u_lhs'_last_arg,wl4)
                                            ->
                                            let lhs'_last_arg =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                u_lhs'_last_arg bs_lhs_args
                                                FStar_Pervasives_Native.None
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____13432 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____13584 =
                                     let uu____13585 =
                                       let uu____13590 =
                                         let uu____13591 =
                                           let uu____13594 =
                                             let uu____13599 =
                                               let uu____13600 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____13600]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____13599
                                              in
                                           uu____13594
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____13591
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____13590)  in
                                     TERM uu____13585  in
                                   [uu____13584]  in
                                 let uu____13621 =
                                   let uu____13628 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____13628 with
                                   | (p1,wl3) ->
                                       let uu____13645 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____13645 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____13621 with
                                  | (sub_probs,wl3) ->
                                      let uu____13672 =
                                        let uu____13673 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____13673  in
                                      solve env1 uu____13672))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____13706 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____13706 with
                | (uu____13721,args) ->
                    (match args with | [] -> false | uu____13749 -> true)
                 in
              let is_arrow rhs2 =
                let uu____13764 =
                  let uu____13765 = FStar_Syntax_Subst.compress rhs2  in
                  uu____13765.FStar_Syntax_Syntax.n  in
                match uu____13764 with
                | FStar_Syntax_Syntax.Tm_arrow uu____13768 -> true
                | uu____13781 -> false  in
              let uu____13782 = quasi_pattern env1 lhs1  in
              match uu____13782 with
              | FStar_Pervasives_Native.None  ->
                  let uu____13793 =
                    let uu____13794 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____13794
                     in
                  giveup_or_defer env1 orig1 wl1 uu____13793
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____13801 = is_app rhs1  in
                  if uu____13801
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____13803 = is_arrow rhs1  in
                     if uu____13803
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____13805 =
                          let uu____13806 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____13806
                           in
                        giveup_or_defer env1 orig1 wl1 uu____13805))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then giveup_or_defer env orig wl "flex-rigid subtyping"
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then giveup_or_defer env orig wl "flex-rigid subtyping"
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____13809 = lhs  in
                (match uu____13809 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____13813 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____13813 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____13828 =
                              let uu____13831 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____13831
                               in
                            FStar_All.pipe_right uu____13828
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____13846 = occurs_check ctx_uv rhs1  in
                          (match uu____13846 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____13868 =
                                   let uu____13869 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____13869
                                    in
                                 giveup_or_defer env orig wl uu____13868
                               else
                                 (let uu____13871 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____13871
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____13876 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____13876
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____13878 =
                                         let uu____13879 =
                                           names_to_string1 fvs2  in
                                         let uu____13880 =
                                           names_to_string1 fvs1  in
                                         let uu____13881 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____13879 uu____13880
                                           uu____13881
                                          in
                                       giveup_or_defer env orig wl
                                         uu____13878)
                                    else first_order orig env wl lhs rhs1))
                      | uu____13887 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____13891 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____13891 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____13914 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____13914
                             | (FStar_Util.Inl msg,uu____13916) ->
                                 first_order orig env wl lhs rhs)))

and (solve_t_flex_flex :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> flex_t -> flex_t -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun lhs  ->
          fun rhs  ->
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then giveup_or_defer env orig wl "flex-flex subtyping"
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then giveup_or_defer env orig wl "flex-flex subtyping"
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then giveup_or_defer env orig wl "flex-flex non-pattern"
                else
                  (let uu____13945 =
                     let uu____13962 = quasi_pattern env lhs  in
                     let uu____13969 = quasi_pattern env rhs  in
                     (uu____13962, uu____13969)  in
                   match uu____13945 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____14012 = lhs  in
                       (match uu____14012 with
                        | ({ FStar_Syntax_Syntax.n = uu____14013;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____14015;_},u_lhs,uu____14017)
                            ->
                            let uu____14020 = rhs  in
                            (match uu____14020 with
                             | (uu____14021,u_rhs,uu____14023) ->
                                 let uu____14024 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____14024
                                 then
                                   let uu____14025 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____14025
                                 else
                                   (let uu____14027 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____14027 with
                                    | (sub_prob,wl1) ->
                                        let uu____14038 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____14038 with
                                         | (ctx_w,(ctx_l,ctx_r)) ->
                                             let gamma_w =
                                               gamma_until
                                                 u_lhs.FStar_Syntax_Syntax.ctx_uvar_gamma
                                                 ctx_w
                                                in
                                             let zs =
                                               intersect_binders
                                                 (FStar_List.append ctx_l
                                                    binders_lhs)
                                                 (FStar_List.append ctx_r
                                                    binders_rhs)
                                                in
                                             let uu____14066 =
                                               let uu____14073 =
                                                 let uu____14076 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____14076
                                                  in
                                               new_uvar
                                                 (Prims.strcat
                                                    "flex-flex quasi: lhs="
                                                    (Prims.strcat
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                       (Prims.strcat ", rhs="
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason)))
                                                 wl1 range gamma_w ctx_w
                                                 uu____14073
                                                 (u_lhs.FStar_Syntax_Syntax.ctx_uvar_should_check
                                                    ||
                                                    u_rhs.FStar_Syntax_Syntax.ctx_uvar_should_check)
                                                in
                                             (match uu____14066 with
                                              | (uu____14079,w,wl2) ->
                                                  let w_app =
                                                    let uu____14085 =
                                                      let uu____14090 =
                                                        FStar_List.map
                                                          (fun uu____14099 
                                                             ->
                                                             match uu____14099
                                                             with
                                                             | (z,uu____14105)
                                                                 ->
                                                                 let uu____14106
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____14106)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____14090
                                                       in
                                                    uu____14085
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____14110 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "Rel")
                                                       in
                                                    if uu____14110
                                                    then
                                                      let uu____14111 =
                                                        flex_t_to_string lhs
                                                         in
                                                      let uu____14112 =
                                                        flex_t_to_string rhs
                                                         in
                                                      let uu____14113 =
                                                        term_to_string w  in
                                                      FStar_Util.print3
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s"
                                                        uu____14111
                                                        uu____14112
                                                        uu____14113
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____14119 =
                                                          let uu____14124 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____14124)
                                                           in
                                                        TERM uu____14119  in
                                                      let uu____14125 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____14125
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____14130 =
                                                             let uu____14135
                                                               =
                                                               FStar_Syntax_Util.abs
                                                                 binders_rhs
                                                                 w_app
                                                                 (FStar_Pervasives_Native.Some
                                                                    (
                                                                    FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                                in
                                                             (u_rhs,
                                                               uu____14135)
                                                              in
                                                           TERM uu____14130
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____14136 =
                                                      let uu____14137 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____14137
                                                       in
                                                    solve env uu____14136)))))))
                   | uu____14138 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           let uu____14206 = head_matches_delta env1 wl1 t1 t2  in
           match uu____14206 with
           | (m,o) ->
               (match (m, o) with
                | (MisMatch uu____14237,uu____14238) ->
                    let rec may_relate head3 =
                      let uu____14265 =
                        let uu____14266 = FStar_Syntax_Subst.compress head3
                           in
                        uu____14266.FStar_Syntax_Syntax.n  in
                      match uu____14265 with
                      | FStar_Syntax_Syntax.Tm_name uu____14269 -> true
                      | FStar_Syntax_Syntax.Tm_match uu____14270 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____14293;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_equational_at_level
                              uu____14294;
                            FStar_Syntax_Syntax.fv_qual = uu____14295;_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____14298;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_abstract uu____14299;
                            FStar_Syntax_Syntax.fv_qual = uu____14300;_}
                          ->
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                      | FStar_Syntax_Syntax.Tm_ascribed
                          (t,uu____14304,uu____14305) -> may_relate t
                      | FStar_Syntax_Syntax.Tm_uinst (t,uu____14347) ->
                          may_relate t
                      | FStar_Syntax_Syntax.Tm_meta (t,uu____14353) ->
                          may_relate t
                      | uu____14358 -> false  in
                    let uu____14359 =
                      ((may_relate head1) || (may_relate head2)) &&
                        wl1.smt_ok
                       in
                    if uu____14359
                    then
                      let uu____14360 =
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then mk_eq2 wl1 orig t1 t2
                        else
                          (let has_type_guard t11 t21 =
                             match problem.FStar_TypeChecker_Common.element
                             with
                             | FStar_Pervasives_Native.Some t ->
                                 FStar_Syntax_Util.mk_has_type t11 t t21
                             | FStar_Pervasives_Native.None  ->
                                 let x =
                                   FStar_Syntax_Syntax.new_bv
                                     FStar_Pervasives_Native.None t11
                                    in
                                 let u_x =
                                   env1.FStar_TypeChecker_Env.universe_of
                                     env1 t11
                                    in
                                 let uu____14392 =
                                   let uu____14393 =
                                     FStar_Syntax_Syntax.bv_to_name x  in
                                   FStar_Syntax_Util.mk_has_type t11
                                     uu____14393 t21
                                    in
                                 FStar_Syntax_Util.mk_forall u_x x
                                   uu____14392
                              in
                           if
                             problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB
                           then
                             let uu____14398 = has_type_guard t1 t2  in
                             (uu____14398, wl1)
                           else
                             (let uu____14404 = has_type_guard t2 t1  in
                              (uu____14404, wl1)))
                         in
                      (match uu____14360 with
                       | (guard,wl2) ->
                           let uu____14411 =
                             solve_prob orig
                               (FStar_Pervasives_Native.Some guard) [] wl2
                              in
                           solve env1 uu____14411)
                    else
                      (let uu____14413 =
                         let uu____14414 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____14415 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.format2 "head mismatch (%s vs %s)"
                           uu____14414 uu____14415
                          in
                       giveup env1 uu____14413 orig)
                | (uu____14416,FStar_Pervasives_Native.Some (t11,t21)) ->
                    solve_t env1
                      (let uu___188_14430 = problem  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___188_14430.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = t11;
                         FStar_TypeChecker_Common.relation =
                           (uu___188_14430.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = t21;
                         FStar_TypeChecker_Common.element =
                           (uu___188_14430.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___188_14430.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___188_14430.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___188_14430.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___188_14430.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___188_14430.FStar_TypeChecker_Common.rank)
                       }) wl1
                | (uu____14431,FStar_Pervasives_Native.None ) ->
                    ((let uu____14443 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____14443
                      then
                        let uu____14444 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____14445 = FStar_Syntax_Print.tag_of_term t1
                           in
                        let uu____14446 =
                          FStar_Syntax_Print.term_to_string t2  in
                        let uu____14447 = FStar_Syntax_Print.tag_of_term t2
                           in
                        FStar_Util.print4
                          "Head matches after call to head_matches_delta: %s (%s) and %s (%s)\n"
                          uu____14444 uu____14445 uu____14446 uu____14447
                      else ());
                     (let uu____14449 = FStar_Syntax_Util.head_and_args t1
                         in
                      match uu____14449 with
                      | (head11,args1) ->
                          let uu____14486 =
                            FStar_Syntax_Util.head_and_args t2  in
                          (match uu____14486 with
                           | (head21,args2) ->
                               let nargs = FStar_List.length args1  in
                               if nargs <> (FStar_List.length args2)
                               then
                                 let uu____14540 =
                                   let uu____14541 =
                                     FStar_Syntax_Print.term_to_string head11
                                      in
                                   let uu____14542 = args_to_string args1  in
                                   let uu____14543 =
                                     FStar_Syntax_Print.term_to_string head21
                                      in
                                   let uu____14544 = args_to_string args2  in
                                   FStar_Util.format4
                                     "unequal number of arguments: %s[%s] and %s[%s]"
                                     uu____14541 uu____14542 uu____14543
                                     uu____14544
                                    in
                                 giveup env1 uu____14540 orig
                               else
                                 (let uu____14546 =
                                    (nargs = (Prims.parse_int "0")) ||
                                      (let uu____14553 =
                                         FStar_Syntax_Util.eq_args args1
                                           args2
                                          in
                                       uu____14553 = FStar_Syntax_Util.Equal)
                                     in
                                  if uu____14546
                                  then
                                    let uu____14554 =
                                      solve_maybe_uinsts env1 orig head11
                                        head21 wl1
                                       in
                                    match uu____14554 with
                                    | USolved wl2 ->
                                        let uu____14556 =
                                          solve_prob orig
                                            FStar_Pervasives_Native.None []
                                            wl2
                                           in
                                        solve env1 uu____14556
                                    | UFailed msg -> giveup env1 msg orig
                                    | UDeferred wl2 ->
                                        solve env1
                                          (defer "universe constraints" orig
                                             wl2)
                                  else
                                    (let uu____14560 =
                                       base_and_refinement env1 t1  in
                                     match uu____14560 with
                                     | (base1,refinement1) ->
                                         let uu____14585 =
                                           base_and_refinement env1 t2  in
                                         (match uu____14585 with
                                          | (base2,refinement2) ->
                                              (match (refinement1,
                                                       refinement2)
                                               with
                                               | (FStar_Pervasives_Native.None
                                                  ,FStar_Pervasives_Native.None
                                                  ) ->
                                                   let uu____14642 =
                                                     solve_maybe_uinsts env1
                                                       orig head11 head21 wl1
                                                      in
                                                   (match uu____14642 with
                                                    | UFailed msg ->
                                                        giveup env1 msg orig
                                                    | UDeferred wl2 ->
                                                        solve env1
                                                          (defer
                                                             "universe constraints"
                                                             orig wl2)
                                                    | USolved wl2 ->
                                                        let uu____14646 =
                                                          FStar_List.fold_right2
                                                            (fun uu____14679 
                                                               ->
                                                               fun
                                                                 uu____14680 
                                                                 ->
                                                                 fun
                                                                   uu____14681
                                                                    ->
                                                                   match 
                                                                    (uu____14679,
                                                                    uu____14680,
                                                                    uu____14681)
                                                                   with
                                                                   | 
                                                                   ((a,uu____14717),
                                                                    (a',uu____14719),
                                                                    (subprobs,wl3))
                                                                    ->
                                                                    let uu____14740
                                                                    =
                                                                    mk_t_problem
                                                                    wl3 []
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a'
                                                                    FStar_Pervasives_Native.None
                                                                    "index"
                                                                     in
                                                                    (match uu____14740
                                                                    with
                                                                    | 
                                                                    (p,wl4)
                                                                    ->
                                                                    ((p ::
                                                                    subprobs),
                                                                    wl4)))
                                                            args1 args2
                                                            ([], wl2)
                                                           in
                                                        (match uu____14646
                                                         with
                                                         | (subprobs,wl3) ->
                                                             ((let uu____14768
                                                                 =
                                                                 FStar_All.pipe_left
                                                                   (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                   (FStar_Options.Other
                                                                    "Rel")
                                                                  in
                                                               if uu____14768
                                                               then
                                                                 let uu____14769
                                                                   =
                                                                   FStar_Syntax_Print.list_to_string
                                                                    (prob_to_string
                                                                    env1)
                                                                    subprobs
                                                                    in
                                                                 FStar_Util.print1
                                                                   "Adding subproblems for arguments: %s\n"
                                                                   uu____14769
                                                               else ());
                                                              (let formula =
                                                                 let uu____14774
                                                                   =
                                                                   FStar_List.map
                                                                    p_guard
                                                                    subprobs
                                                                    in
                                                                 FStar_Syntax_Util.mk_conj_l
                                                                   uu____14774
                                                                  in
                                                               let wl4 =
                                                                 solve_prob
                                                                   orig
                                                                   (FStar_Pervasives_Native.Some
                                                                    formula)
                                                                   [] wl3
                                                                  in
                                                               solve env1
                                                                 (attempt
                                                                    subprobs
                                                                    wl4)))))
                                               | uu____14782 ->
                                                   let lhs =
                                                     force_refinement
                                                       (base1, refinement1)
                                                      in
                                                   let rhs =
                                                     force_refinement
                                                       (base2, refinement2)
                                                      in
                                                   solve_t env1
                                                     (let uu___189_14822 =
                                                        problem  in
                                                      {
                                                        FStar_TypeChecker_Common.pid
                                                          =
                                                          (uu___189_14822.FStar_TypeChecker_Common.pid);
                                                        FStar_TypeChecker_Common.lhs
                                                          = lhs;
                                                        FStar_TypeChecker_Common.relation
                                                          =
                                                          (uu___189_14822.FStar_TypeChecker_Common.relation);
                                                        FStar_TypeChecker_Common.rhs
                                                          = rhs;
                                                        FStar_TypeChecker_Common.element
                                                          =
                                                          (uu___189_14822.FStar_TypeChecker_Common.element);
                                                        FStar_TypeChecker_Common.logical_guard
                                                          =
                                                          (uu___189_14822.FStar_TypeChecker_Common.logical_guard);
                                                        FStar_TypeChecker_Common.logical_guard_uvar
                                                          =
                                                          (uu___189_14822.FStar_TypeChecker_Common.logical_guard_uvar);
                                                        FStar_TypeChecker_Common.reason
                                                          =
                                                          (uu___189_14822.FStar_TypeChecker_Common.reason);
                                                        FStar_TypeChecker_Common.loc
                                                          =
                                                          (uu___189_14822.FStar_TypeChecker_Common.loc);
                                                        FStar_TypeChecker_Common.rank
                                                          =
                                                          (uu___189_14822.FStar_TypeChecker_Common.rank)
                                                      }) wl1))))))))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____14825 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____14825
          then
            let uu____14826 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____14826
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____14831 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____14831
              then
                let uu____14832 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____14833 =
                  let uu____14834 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____14835 =
                    let uu____14836 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.strcat "::" uu____14836  in
                  Prims.strcat uu____14834 uu____14835  in
                let uu____14837 =
                  let uu____14838 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____14839 =
                    let uu____14840 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.strcat "::" uu____14840  in
                  Prims.strcat uu____14838 uu____14839  in
                FStar_Util.print3 "Attempting %s (%s vs %s)\n" uu____14832
                  uu____14833 uu____14837
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____14843,uu____14844) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____14869,FStar_Syntax_Syntax.Tm_delayed uu____14870) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____14895,uu____14896) ->
                  let uu____14923 =
                    let uu___190_14924 = problem  in
                    let uu____14925 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___190_14924.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____14925;
                      FStar_TypeChecker_Common.relation =
                        (uu___190_14924.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___190_14924.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___190_14924.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___190_14924.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___190_14924.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___190_14924.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___190_14924.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___190_14924.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____14923 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____14926,uu____14927) ->
                  let uu____14934 =
                    let uu___191_14935 = problem  in
                    let uu____14936 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___191_14935.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____14936;
                      FStar_TypeChecker_Common.relation =
                        (uu___191_14935.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___191_14935.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___191_14935.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___191_14935.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___191_14935.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___191_14935.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___191_14935.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___191_14935.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____14934 wl
              | (uu____14937,FStar_Syntax_Syntax.Tm_ascribed uu____14938) ->
                  let uu____14965 =
                    let uu___192_14966 = problem  in
                    let uu____14967 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___192_14966.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___192_14966.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___192_14966.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____14967;
                      FStar_TypeChecker_Common.element =
                        (uu___192_14966.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___192_14966.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___192_14966.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___192_14966.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___192_14966.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___192_14966.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____14965 wl
              | (uu____14968,FStar_Syntax_Syntax.Tm_meta uu____14969) ->
                  let uu____14976 =
                    let uu___193_14977 = problem  in
                    let uu____14978 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___193_14977.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___193_14977.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___193_14977.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____14978;
                      FStar_TypeChecker_Common.element =
                        (uu___193_14977.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___193_14977.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___193_14977.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___193_14977.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___193_14977.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___193_14977.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____14976 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____14980),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____14982)) ->
                  let uu____14991 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____14991
              | (FStar_Syntax_Syntax.Tm_bvar uu____14992,uu____14993) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____14994,FStar_Syntax_Syntax.Tm_bvar uu____14995) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___148_15054 =
                    match uu___148_15054 with
                    | [] -> c
                    | bs ->
                        let uu____15076 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____15076
                     in
                  let uu____15085 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____15085 with
                   | ((bs11,c11),(bs21,c21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let c12 =
                                    FStar_Syntax_Subst.subst_comp subst1 c11
                                     in
                                  let c22 =
                                    FStar_Syntax_Subst.subst_comp subst1 c21
                                     in
                                  let rel =
                                    let uu____15208 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____15208
                                    then FStar_TypeChecker_Common.EQ
                                    else
                                      problem.FStar_TypeChecker_Common.relation
                                     in
                                  mk_c_problem wl1 scope orig c12 rel c22
                                    FStar_Pervasives_Native.None
                                    "function co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs
                 (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                 (bs2,tbody2,lopt2)) ->
                  let mk_t t l uu___149_15283 =
                    match uu___149_15283 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____15317 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____15317 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____15436 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____15437 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____15436
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____15437 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____15438,uu____15439) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____15466 -> true
                    | uu____15483 -> false  in
                  let maybe_eta t =
                    if is_abs t
                    then FStar_Util.Inl t
                    else
                      (let t3 =
                         FStar_TypeChecker_Normalize.eta_expand wl.tcenv t
                          in
                       if is_abs t3
                       then FStar_Util.Inl t3
                       else FStar_Util.Inr t3)
                     in
                  let force_eta t =
                    if is_abs t
                    then t
                    else
                      (let uu____15524 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___194_15532 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___194_15532.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___194_15532.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___194_15532.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___194_15532.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___194_15532.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___194_15532.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___194_15532.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___194_15532.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___194_15532.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___194_15532.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___194_15532.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___194_15532.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___194_15532.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___194_15532.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___194_15532.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___194_15532.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___194_15532.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___194_15532.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___194_15532.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___194_15532.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___194_15532.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___194_15532.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___194_15532.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___194_15532.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___194_15532.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___194_15532.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___194_15532.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___194_15532.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___194_15532.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___194_15532.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___194_15532.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___194_15532.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___194_15532.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___194_15532.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___194_15532.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____15524 with
                       | (uu____15535,ty,uu____15537) ->
                           let uu____15538 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____15538)
                     in
                  let uu____15539 =
                    let uu____15552 = maybe_eta t1  in
                    let uu____15557 = maybe_eta t2  in
                    (uu____15552, uu____15557)  in
                  (match uu____15539 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___195_15581 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___195_15581.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___195_15581.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___195_15581.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___195_15581.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___195_15581.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___195_15581.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___195_15581.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___195_15581.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____15592 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____15592
                       then
                         let uu____15593 = destruct_flex_t not_abs wl  in
                         (match uu____15593 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___196_15608 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___196_15608.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___196_15608.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___196_15608.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___196_15608.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___196_15608.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___196_15608.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___196_15608.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___196_15608.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____15620 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____15620
                       then
                         let uu____15621 = destruct_flex_t not_abs wl  in
                         (match uu____15621 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___196_15636 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___196_15636.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___196_15636.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___196_15636.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___196_15636.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___196_15636.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___196_15636.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___196_15636.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___196_15636.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____15638 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____15651,FStar_Syntax_Syntax.Tm_abs uu____15652) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____15679 -> true
                    | uu____15696 -> false  in
                  let maybe_eta t =
                    if is_abs t
                    then FStar_Util.Inl t
                    else
                      (let t3 =
                         FStar_TypeChecker_Normalize.eta_expand wl.tcenv t
                          in
                       if is_abs t3
                       then FStar_Util.Inl t3
                       else FStar_Util.Inr t3)
                     in
                  let force_eta t =
                    if is_abs t
                    then t
                    else
                      (let uu____15737 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___194_15745 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___194_15745.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___194_15745.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___194_15745.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___194_15745.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___194_15745.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___194_15745.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___194_15745.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___194_15745.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___194_15745.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___194_15745.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___194_15745.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___194_15745.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___194_15745.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___194_15745.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___194_15745.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___194_15745.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___194_15745.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___194_15745.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___194_15745.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___194_15745.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___194_15745.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___194_15745.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___194_15745.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___194_15745.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___194_15745.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___194_15745.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___194_15745.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___194_15745.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___194_15745.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___194_15745.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___194_15745.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___194_15745.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___194_15745.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___194_15745.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___194_15745.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____15737 with
                       | (uu____15748,ty,uu____15750) ->
                           let uu____15751 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____15751)
                     in
                  let uu____15752 =
                    let uu____15765 = maybe_eta t1  in
                    let uu____15770 = maybe_eta t2  in
                    (uu____15765, uu____15770)  in
                  (match uu____15752 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___195_15794 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___195_15794.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___195_15794.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___195_15794.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___195_15794.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___195_15794.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___195_15794.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___195_15794.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___195_15794.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____15805 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____15805
                       then
                         let uu____15806 = destruct_flex_t not_abs wl  in
                         (match uu____15806 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___196_15821 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___196_15821.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___196_15821.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___196_15821.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___196_15821.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___196_15821.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___196_15821.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___196_15821.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___196_15821.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____15833 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____15833
                       then
                         let uu____15834 = destruct_flex_t not_abs wl  in
                         (match uu____15834 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___196_15849 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___196_15849.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___196_15849.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___196_15849.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___196_15849.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___196_15849.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___196_15849.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___196_15849.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___196_15849.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____15851 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let should_delta =
                    ((let uu____15879 = FStar_Syntax_Free.uvars t1  in
                      FStar_Util.set_is_empty uu____15879) &&
                       (let uu____15883 = FStar_Syntax_Free.uvars t2  in
                        FStar_Util.set_is_empty uu____15883))
                      &&
                      (let uu____15890 =
                         head_matches env x1.FStar_Syntax_Syntax.sort
                           x2.FStar_Syntax_Syntax.sort
                          in
                       match uu____15890 with
                       | MisMatch
                           (FStar_Pervasives_Native.Some
                            d1,FStar_Pervasives_Native.Some d2)
                           ->
                           let is_unfoldable uu___150_15902 =
                             match uu___150_15902 with
                             | FStar_Syntax_Syntax.Delta_constant_at_level
                                 uu____15903 -> true
                             | uu____15904 -> false  in
                           (is_unfoldable d1) && (is_unfoldable d2)
                       | uu____15905 -> false)
                     in
                  let uu____15906 = as_refinement should_delta env wl t1  in
                  (match uu____15906 with
                   | (x11,phi1) ->
                       let uu____15913 = as_refinement should_delta env wl t2
                          in
                       (match uu____15913 with
                        | (x21,phi21) ->
                            let uu____15920 =
                              mk_t_problem wl [] orig
                                x11.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.relation
                                x21.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.element
                                "refinement base type"
                               in
                            (match uu____15920 with
                             | (base_prob,wl1) ->
                                 let x12 = FStar_Syntax_Syntax.freshen_bv x11
                                    in
                                 let subst1 =
                                   [FStar_Syntax_Syntax.DB
                                      ((Prims.parse_int "0"), x12)]
                                    in
                                 let phi11 =
                                   FStar_Syntax_Subst.subst subst1 phi1  in
                                 let phi22 =
                                   FStar_Syntax_Subst.subst subst1 phi21  in
                                 let env1 =
                                   FStar_TypeChecker_Env.push_bv env x12  in
                                 let mk_imp1 imp phi12 phi23 =
                                   let uu____15986 = imp phi12 phi23  in
                                   FStar_All.pipe_right uu____15986
                                     (guard_on_element wl1 problem x12)
                                    in
                                 let fallback uu____15998 =
                                   let impl =
                                     if
                                       problem.FStar_TypeChecker_Common.relation
                                         = FStar_TypeChecker_Common.EQ
                                     then
                                       mk_imp1 FStar_Syntax_Util.mk_iff phi11
                                         phi22
                                     else
                                       mk_imp1 FStar_Syntax_Util.mk_imp phi11
                                         phi22
                                      in
                                   let guard =
                                     FStar_Syntax_Util.mk_conj
                                       (p_guard base_prob) impl
                                      in
                                   let wl2 =
                                     solve_prob orig
                                       (FStar_Pervasives_Native.Some guard)
                                       [] wl1
                                      in
                                   solve env1 (attempt [base_prob] wl2)  in
                                 if
                                   problem.FStar_TypeChecker_Common.relation
                                     = FStar_TypeChecker_Common.EQ
                                 then
                                   let uu____16009 =
                                     let uu____16014 =
                                       let uu____16021 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____16021]  in
                                     mk_t_problem wl1 uu____16014 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   (match uu____16009 with
                                    | (ref_prob,wl2) ->
                                        let uu____16036 =
                                          solve env1
                                            (let uu___197_16038 = wl2  in
                                             {
                                               attempting = [ref_prob];
                                               wl_deferred = [];
                                               ctr = (uu___197_16038.ctr);
                                               defer_ok = false;
                                               smt_ok =
                                                 (uu___197_16038.smt_ok);
                                               tcenv = (uu___197_16038.tcenv);
                                               wl_implicits =
                                                 (uu___197_16038.wl_implicits)
                                             })
                                           in
                                        (match uu____16036 with
                                         | Failed uu____16045 -> fallback ()
                                         | Success uu____16050 ->
                                             let guard =
                                               let uu____16058 =
                                                 FStar_All.pipe_right
                                                   (p_guard ref_prob)
                                                   (guard_on_element wl2
                                                      problem x12)
                                                  in
                                               FStar_Syntax_Util.mk_conj
                                                 (p_guard base_prob)
                                                 uu____16058
                                                in
                                             let wl3 =
                                               solve_prob orig
                                                 (FStar_Pervasives_Native.Some
                                                    guard) [] wl2
                                                in
                                             let wl4 =
                                               let uu___198_16067 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___198_16067.attempting);
                                                 wl_deferred =
                                                   (uu___198_16067.wl_deferred);
                                                 ctr =
                                                   (wl3.ctr +
                                                      (Prims.parse_int "1"));
                                                 defer_ok =
                                                   (uu___198_16067.defer_ok);
                                                 smt_ok =
                                                   (uu___198_16067.smt_ok);
                                                 tcenv =
                                                   (uu___198_16067.tcenv);
                                                 wl_implicits =
                                                   (uu___198_16067.wl_implicits)
                                               }  in
                                             solve env1
                                               (attempt [base_prob] wl4)))
                                 else fallback ())))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16069,FStar_Syntax_Syntax.Tm_uvar uu____16070) ->
                  let uu____16083 = destruct_flex_t t1 wl  in
                  (match uu____16083 with
                   | (f1,wl1) ->
                       let uu____16090 = destruct_flex_t t2 wl1  in
                       (match uu____16090 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16097;
                    FStar_Syntax_Syntax.pos = uu____16098;
                    FStar_Syntax_Syntax.vars = uu____16099;_},uu____16100),FStar_Syntax_Syntax.Tm_uvar
                 uu____16101) ->
                  let uu____16134 = destruct_flex_t t1 wl  in
                  (match uu____16134 with
                   | (f1,wl1) ->
                       let uu____16141 = destruct_flex_t t2 wl1  in
                       (match uu____16141 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16148,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16149;
                    FStar_Syntax_Syntax.pos = uu____16150;
                    FStar_Syntax_Syntax.vars = uu____16151;_},uu____16152))
                  ->
                  let uu____16185 = destruct_flex_t t1 wl  in
                  (match uu____16185 with
                   | (f1,wl1) ->
                       let uu____16192 = destruct_flex_t t2 wl1  in
                       (match uu____16192 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16199;
                    FStar_Syntax_Syntax.pos = uu____16200;
                    FStar_Syntax_Syntax.vars = uu____16201;_},uu____16202),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16203;
                    FStar_Syntax_Syntax.pos = uu____16204;
                    FStar_Syntax_Syntax.vars = uu____16205;_},uu____16206))
                  ->
                  let uu____16259 = destruct_flex_t t1 wl  in
                  (match uu____16259 with
                   | (f1,wl1) ->
                       let uu____16266 = destruct_flex_t t2 wl1  in
                       (match uu____16266 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____16273,uu____16274) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____16281 = destruct_flex_t t1 wl  in
                  (match uu____16281 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16288;
                    FStar_Syntax_Syntax.pos = uu____16289;
                    FStar_Syntax_Syntax.vars = uu____16290;_},uu____16291),uu____16292)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____16319 = destruct_flex_t t1 wl  in
                  (match uu____16319 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____16326,FStar_Syntax_Syntax.Tm_uvar uu____16327) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____16334,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16335;
                    FStar_Syntax_Syntax.pos = uu____16336;
                    FStar_Syntax_Syntax.vars = uu____16337;_},uu____16338))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____16365,FStar_Syntax_Syntax.Tm_arrow uu____16366) ->
                  solve_t' env
                    (let uu___199_16386 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___199_16386.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___199_16386.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___199_16386.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___199_16386.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___199_16386.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___199_16386.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___199_16386.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___199_16386.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___199_16386.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16387;
                    FStar_Syntax_Syntax.pos = uu____16388;
                    FStar_Syntax_Syntax.vars = uu____16389;_},uu____16390),FStar_Syntax_Syntax.Tm_arrow
                 uu____16391) ->
                  solve_t' env
                    (let uu___199_16431 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___199_16431.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___199_16431.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___199_16431.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___199_16431.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___199_16431.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___199_16431.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___199_16431.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___199_16431.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___199_16431.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____16432,FStar_Syntax_Syntax.Tm_uvar uu____16433) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (uu____16440,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16441;
                    FStar_Syntax_Syntax.pos = uu____16442;
                    FStar_Syntax_Syntax.vars = uu____16443;_},uu____16444))
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_uvar uu____16471,uu____16472) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____16479;
                    FStar_Syntax_Syntax.pos = uu____16480;
                    FStar_Syntax_Syntax.vars = uu____16481;_},uu____16482),uu____16483)
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_refine uu____16510,uu____16511) ->
                  let t21 =
                    let uu____16519 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____16519  in
                  solve_t env
                    (let uu___200_16545 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___200_16545.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___200_16545.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___200_16545.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___200_16545.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___200_16545.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___200_16545.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___200_16545.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___200_16545.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___200_16545.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____16546,FStar_Syntax_Syntax.Tm_refine uu____16547) ->
                  let t11 =
                    let uu____16555 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____16555  in
                  solve_t env
                    (let uu___201_16581 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___201_16581.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___201_16581.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___201_16581.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___201_16581.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___201_16581.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___201_16581.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___201_16581.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___201_16581.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___201_16581.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (t11,brs1),FStar_Syntax_Syntax.Tm_match (t21,brs2)) ->
                  let uu____16658 =
                    mk_t_problem wl [] orig t11 FStar_TypeChecker_Common.EQ
                      t21 FStar_Pervasives_Native.None "match scrutinee"
                     in
                  (match uu____16658 with
                   | (sc_prob,wl1) ->
                       let rec solve_branches wl2 brs11 brs21 =
                         match (brs11, brs21) with
                         | (br1::rs1,br2::rs2) ->
                             let uu____16879 = br1  in
                             (match uu____16879 with
                              | (p1,w1,uu____16904) ->
                                  let uu____16921 = br2  in
                                  (match uu____16921 with
                                   | (p2,w2,uu____16940) ->
                                       let uu____16945 =
                                         let uu____16946 =
                                           FStar_Syntax_Syntax.eq_pat p1 p2
                                            in
                                         Prims.op_Negation uu____16946  in
                                       if uu____16945
                                       then FStar_Pervasives_Native.None
                                       else
                                         (let uu____16962 =
                                            FStar_Syntax_Subst.open_branch'
                                              br1
                                             in
                                          match uu____16962 with
                                          | ((p11,w11,e1),s) ->
                                              let uu____16995 = br2  in
                                              (match uu____16995 with
                                               | (p21,w21,e2) ->
                                                   let w22 =
                                                     FStar_Util.map_opt w21
                                                       (FStar_Syntax_Subst.subst
                                                          s)
                                                      in
                                                   let e21 =
                                                     FStar_Syntax_Subst.subst
                                                       s e2
                                                      in
                                                   let scope =
                                                     let uu____17030 =
                                                       FStar_Syntax_Syntax.pat_bvs
                                                         p11
                                                        in
                                                     FStar_All.pipe_left
                                                       (FStar_List.map
                                                          FStar_Syntax_Syntax.mk_binder)
                                                       uu____17030
                                                      in
                                                   let uu____17041 =
                                                     match (w11, w22) with
                                                     | (FStar_Pervasives_Native.Some
                                                        uu____17064,FStar_Pervasives_Native.None
                                                        ) ->
                                                         FStar_Pervasives_Native.None
                                                     | (FStar_Pervasives_Native.None
                                                        ,FStar_Pervasives_Native.Some
                                                        uu____17081) ->
                                                         FStar_Pervasives_Native.None
                                                     | (FStar_Pervasives_Native.None
                                                        ,FStar_Pervasives_Native.None
                                                        ) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([], wl2)
                                                     | (FStar_Pervasives_Native.Some
                                                        w12,FStar_Pervasives_Native.Some
                                                        w23) ->
                                                         let uu____17124 =
                                                           mk_t_problem wl2
                                                             scope orig w12
                                                             FStar_TypeChecker_Common.EQ
                                                             w23
                                                             FStar_Pervasives_Native.None
                                                             "when clause"
                                                            in
                                                         (match uu____17124
                                                          with
                                                          | (p,wl3) ->
                                                              FStar_Pervasives_Native.Some
                                                                ([p], wl3))
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____17041
                                                     (fun uu____17166  ->
                                                        match uu____17166
                                                        with
                                                        | (wprobs,wl3) ->
                                                            let uu____17187 =
                                                              mk_t_problem
                                                                wl3 scope
                                                                orig e1
                                                                FStar_TypeChecker_Common.EQ
                                                                e21
                                                                FStar_Pervasives_Native.None
                                                                "branch body"
                                                               in
                                                            (match uu____17187
                                                             with
                                                             | (prob,wl4) ->
                                                                 let uu____17202
                                                                   =
                                                                   solve_branches
                                                                    wl4 rs1
                                                                    rs2
                                                                    in
                                                                 FStar_Util.bind_opt
                                                                   uu____17202
                                                                   (fun
                                                                    uu____17226
                                                                     ->
                                                                    match uu____17226
                                                                    with
                                                                    | 
                                                                    (r1,wl5)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    ((prob ::
                                                                    (FStar_List.append
                                                                    wprobs r1)),
                                                                    wl5))))))))
                         | ([],[]) -> FStar_Pervasives_Native.Some ([], wl2)
                         | uu____17311 -> FStar_Pervasives_Native.None  in
                       let uu____17348 = solve_branches wl1 brs1 brs2  in
                       (match uu____17348 with
                        | FStar_Pervasives_Native.None  ->
                            giveup env "Tm_match branches don't match" orig
                        | FStar_Pervasives_Native.Some (sub_probs,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let wl3 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl2
                               in
                            solve env (attempt sub_probs1 wl3)))
              | (FStar_Syntax_Syntax.Tm_match uu____17379,uu____17380) ->
                  let head1 =
                    let uu____17404 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17404
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17444 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17444
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17484 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____17484
                    then
                      let uu____17485 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17486 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17487 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17485 uu____17486 uu____17487
                    else ());
                   (let uu____17489 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17489
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17496 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17496
                       then
                         let uu____17497 =
                           let uu____17504 =
                             let uu____17505 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17505 = FStar_Syntax_Util.Equal  in
                           if uu____17504
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17515 = mk_eq2 wl orig t1 t2  in
                              match uu____17515 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17497 with
                         | (guard,wl1) ->
                             let uu____17536 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17536
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____17539,uu____17540) ->
                  let head1 =
                    let uu____17548 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17548
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17588 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17588
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17628 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____17628
                    then
                      let uu____17629 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17630 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17631 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17629 uu____17630 uu____17631
                    else ());
                   (let uu____17633 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17633
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17640 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17640
                       then
                         let uu____17641 =
                           let uu____17648 =
                             let uu____17649 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17649 = FStar_Syntax_Util.Equal  in
                           if uu____17648
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17659 = mk_eq2 wl orig t1 t2  in
                              match uu____17659 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17641 with
                         | (guard,wl1) ->
                             let uu____17680 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17680
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____17683,uu____17684) ->
                  let head1 =
                    let uu____17686 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17686
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17726 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17726
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17766 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____17766
                    then
                      let uu____17767 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17768 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17769 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17767 uu____17768 uu____17769
                    else ());
                   (let uu____17771 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17771
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17778 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17778
                       then
                         let uu____17779 =
                           let uu____17786 =
                             let uu____17787 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17787 = FStar_Syntax_Util.Equal  in
                           if uu____17786
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17797 = mk_eq2 wl orig t1 t2  in
                              match uu____17797 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17779 with
                         | (guard,wl1) ->
                             let uu____17818 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17818
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____17821,uu____17822) ->
                  let head1 =
                    let uu____17824 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17824
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17864 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17864
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17904 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____17904
                    then
                      let uu____17905 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17906 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17907 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17905 uu____17906 uu____17907
                    else ());
                   (let uu____17909 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17909
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17916 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17916
                       then
                         let uu____17917 =
                           let uu____17924 =
                             let uu____17925 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17925 = FStar_Syntax_Util.Equal  in
                           if uu____17924
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17935 = mk_eq2 wl orig t1 t2  in
                              match uu____17935 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17917 with
                         | (guard,wl1) ->
                             let uu____17956 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17956
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____17959,uu____17960) ->
                  let head1 =
                    let uu____17962 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17962
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18002 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18002
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18042 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18042
                    then
                      let uu____18043 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18044 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18045 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18043 uu____18044 uu____18045
                    else ());
                   (let uu____18047 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18047
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18054 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18054
                       then
                         let uu____18055 =
                           let uu____18062 =
                             let uu____18063 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18063 = FStar_Syntax_Util.Equal  in
                           if uu____18062
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18073 = mk_eq2 wl orig t1 t2  in
                              match uu____18073 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18055 with
                         | (guard,wl1) ->
                             let uu____18094 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18094
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____18097,uu____18098) ->
                  let head1 =
                    let uu____18114 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18114
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18154 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18154
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18194 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18194
                    then
                      let uu____18195 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18196 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18197 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18195 uu____18196 uu____18197
                    else ());
                   (let uu____18199 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18199
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18206 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18206
                       then
                         let uu____18207 =
                           let uu____18214 =
                             let uu____18215 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18215 = FStar_Syntax_Util.Equal  in
                           if uu____18214
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18225 = mk_eq2 wl orig t1 t2  in
                              match uu____18225 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18207 with
                         | (guard,wl1) ->
                             let uu____18246 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18246
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____18249,FStar_Syntax_Syntax.Tm_match uu____18250) ->
                  let head1 =
                    let uu____18274 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18274
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18314 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18314
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18354 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18354
                    then
                      let uu____18355 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18356 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18357 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18355 uu____18356 uu____18357
                    else ());
                   (let uu____18359 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18359
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18366 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18366
                       then
                         let uu____18367 =
                           let uu____18374 =
                             let uu____18375 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18375 = FStar_Syntax_Util.Equal  in
                           if uu____18374
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18385 = mk_eq2 wl orig t1 t2  in
                              match uu____18385 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18367 with
                         | (guard,wl1) ->
                             let uu____18406 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18406
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____18409,FStar_Syntax_Syntax.Tm_uinst uu____18410) ->
                  let head1 =
                    let uu____18418 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18418
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18458 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18458
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18498 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18498
                    then
                      let uu____18499 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18500 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18501 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18499 uu____18500 uu____18501
                    else ());
                   (let uu____18503 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18503
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18510 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18510
                       then
                         let uu____18511 =
                           let uu____18518 =
                             let uu____18519 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18519 = FStar_Syntax_Util.Equal  in
                           if uu____18518
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18529 = mk_eq2 wl orig t1 t2  in
                              match uu____18529 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18511 with
                         | (guard,wl1) ->
                             let uu____18550 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18550
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____18553,FStar_Syntax_Syntax.Tm_name uu____18554) ->
                  let head1 =
                    let uu____18556 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18556
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18596 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18596
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18636 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18636
                    then
                      let uu____18637 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18638 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18639 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18637 uu____18638 uu____18639
                    else ());
                   (let uu____18641 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18641
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18648 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18648
                       then
                         let uu____18649 =
                           let uu____18656 =
                             let uu____18657 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18657 = FStar_Syntax_Util.Equal  in
                           if uu____18656
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18667 = mk_eq2 wl orig t1 t2  in
                              match uu____18667 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18649 with
                         | (guard,wl1) ->
                             let uu____18688 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18688
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____18691,FStar_Syntax_Syntax.Tm_constant uu____18692) ->
                  let head1 =
                    let uu____18694 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18694
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18734 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18734
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18774 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18774
                    then
                      let uu____18775 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18776 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18777 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18775 uu____18776 uu____18777
                    else ());
                   (let uu____18779 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18779
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18786 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18786
                       then
                         let uu____18787 =
                           let uu____18794 =
                             let uu____18795 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18795 = FStar_Syntax_Util.Equal  in
                           if uu____18794
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18805 = mk_eq2 wl orig t1 t2  in
                              match uu____18805 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18787 with
                         | (guard,wl1) ->
                             let uu____18826 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18826
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____18829,FStar_Syntax_Syntax.Tm_fvar uu____18830) ->
                  let head1 =
                    let uu____18832 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18832
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____18872 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____18872
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____18912 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____18912
                    then
                      let uu____18913 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____18914 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____18915 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____18913 uu____18914 uu____18915
                    else ());
                   (let uu____18917 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____18917
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____18924 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____18924
                       then
                         let uu____18925 =
                           let uu____18932 =
                             let uu____18933 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____18933 = FStar_Syntax_Util.Equal  in
                           if uu____18932
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____18943 = mk_eq2 wl orig t1 t2  in
                              match uu____18943 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____18925 with
                         | (guard,wl1) ->
                             let uu____18964 = solve_prob orig guard [] wl1
                                in
                             solve env uu____18964
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____18967,FStar_Syntax_Syntax.Tm_app uu____18968) ->
                  let head1 =
                    let uu____18984 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____18984
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____19024 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____19024
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____19064 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____19064
                    then
                      let uu____19065 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____19066 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____19067 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____19065 uu____19066 uu____19067
                    else ());
                   (let uu____19069 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____19069
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____19076 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____19076
                       then
                         let uu____19077 =
                           let uu____19084 =
                             let uu____19085 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____19085 = FStar_Syntax_Util.Equal  in
                           if uu____19084
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____19095 = mk_eq2 wl orig t1 t2  in
                              match uu____19095 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____19077 with
                         | (guard,wl1) ->
                             let uu____19116 = solve_prob orig guard [] wl1
                                in
                             solve env uu____19116
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____19119,FStar_Syntax_Syntax.Tm_let uu____19120) ->
                  let uu____19145 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____19145
                  then
                    let uu____19146 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____19146
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____19148,uu____19149) ->
                  let uu____19162 =
                    let uu____19167 =
                      let uu____19168 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____19169 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____19170 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____19171 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____19168 uu____19169 uu____19170 uu____19171
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____19167)
                     in
                  FStar_Errors.raise_error uu____19162
                    t1.FStar_Syntax_Syntax.pos
              | (uu____19172,FStar_Syntax_Syntax.Tm_let uu____19173) ->
                  let uu____19186 =
                    let uu____19191 =
                      let uu____19192 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____19193 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____19194 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____19195 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____19192 uu____19193 uu____19194 uu____19195
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____19191)
                     in
                  FStar_Errors.raise_error uu____19186
                    t1.FStar_Syntax_Syntax.pos
              | uu____19196 -> giveup env "head tag mismatch" orig))))

and (solve_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem ->
      worklist -> solution)
  =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let c1 = problem.FStar_TypeChecker_Common.lhs  in
        let c2 = problem.FStar_TypeChecker_Common.rhs  in
        let orig = FStar_TypeChecker_Common.CProb problem  in
        let sub_prob wl1 t1 rel t2 reason =
          mk_t_problem wl1 [] orig t1 rel t2 FStar_Pervasives_Native.None
            reason
           in
        let solve_eq c1_comp c2_comp =
          (let uu____19255 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____19255
           then
             let uu____19256 =
               let uu____19257 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____19257  in
             let uu____19258 =
               let uu____19259 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____19259  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____19256 uu____19258
           else ());
          (let uu____19261 =
             let uu____19262 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____19262  in
           if uu____19261
           then
             let uu____19263 =
               let uu____19264 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____19265 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____19264 uu____19265
                in
             giveup env uu____19263 orig
           else
             (let uu____19267 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____19267 with
              | (ret_sub_prob,wl1) ->
                  let uu____19274 =
                    FStar_List.fold_right2
                      (fun uu____19307  ->
                         fun uu____19308  ->
                           fun uu____19309  ->
                             match (uu____19307, uu____19308, uu____19309)
                             with
                             | ((a1,uu____19345),(a2,uu____19347),(arg_sub_probs,wl2))
                                 ->
                                 let uu____19368 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____19368 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____19274 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____19397 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____19397  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       solve env (attempt sub_probs wl3))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____19427 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____19430)::[] -> wp1
              | uu____19447 ->
                  let uu____19456 =
                    let uu____19457 =
                      let uu____19458 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____19458  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____19457
                     in
                  failwith uu____19456
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____19464 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____19464]
              | x -> x  in
            let uu____19466 =
              let uu____19475 =
                let uu____19482 =
                  let uu____19483 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____19483 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____19482  in
              [uu____19475]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____19466;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____19496 = lift_c1 ()  in solve_eq uu____19496 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___151_19502  ->
                       match uu___151_19502 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____19503 -> false))
                in
             let uu____19504 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____19530)::uu____19531,(wp2,uu____19533)::uu____19534)
                   -> (wp1, wp2)
               | uu____19587 ->
                   let uu____19608 =
                     let uu____19613 =
                       let uu____19614 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____19615 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____19614 uu____19615
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____19613)
                      in
                   FStar_Errors.raise_error uu____19608
                     env.FStar_TypeChecker_Env.range
                in
             match uu____19504 with
             | (wpc1,wpc2) ->
                 let uu____19622 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____19622
                 then
                   let uu____19625 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____19625 wl
                 else
                   (let uu____19627 =
                      let uu____19634 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____19634  in
                    match uu____19627 with
                    | (c2_decl,qualifiers) ->
                        let uu____19655 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____19655
                        then
                          let c1_repr =
                            let uu____19659 =
                              let uu____19660 =
                                let uu____19661 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____19661  in
                              let uu____19662 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____19660 uu____19662
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____19659
                             in
                          let c2_repr =
                            let uu____19664 =
                              let uu____19665 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____19666 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____19665 uu____19666
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____19664
                             in
                          let uu____19667 =
                            let uu____19672 =
                              let uu____19673 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____19674 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____19673 uu____19674
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____19672
                             in
                          (match uu____19667 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               solve env (attempt [prob] wl2))
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____19688 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____19688
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____19691 =
                                     let uu____19698 =
                                       let uu____19699 =
                                         let uu____19714 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____19717 =
                                           let uu____19726 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____19733 =
                                             let uu____19742 =
                                               let uu____19749 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____19749
                                                in
                                             [uu____19742]  in
                                           uu____19726 :: uu____19733  in
                                         (uu____19714, uu____19717)  in
                                       FStar_Syntax_Syntax.Tm_app uu____19699
                                        in
                                     FStar_Syntax_Syntax.mk uu____19698  in
                                   uu____19691 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____19784 =
                                    let uu____19791 =
                                      let uu____19792 =
                                        let uu____19807 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____19810 =
                                          let uu____19819 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____19826 =
                                            let uu____19835 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____19842 =
                                              let uu____19851 =
                                                let uu____19858 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____19858
                                                 in
                                              [uu____19851]  in
                                            uu____19835 :: uu____19842  in
                                          uu____19819 :: uu____19826  in
                                        (uu____19807, uu____19810)  in
                                      FStar_Syntax_Syntax.Tm_app uu____19792
                                       in
                                    FStar_Syntax_Syntax.mk uu____19791  in
                                  uu____19784 FStar_Pervasives_Native.None r)
                              in
                           let uu____19896 =
                             sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                               problem.FStar_TypeChecker_Common.relation
                               c21.FStar_Syntax_Syntax.result_typ
                               "result type"
                              in
                           match uu____19896 with
                           | (base_prob,wl1) ->
                               let wl2 =
                                 let uu____19904 =
                                   let uu____19907 =
                                     FStar_Syntax_Util.mk_conj
                                       (p_guard base_prob) g
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_26  ->
                                        FStar_Pervasives_Native.Some _0_26)
                                     uu____19907
                                    in
                                 solve_prob orig uu____19904 [] wl1  in
                               solve env (attempt [base_prob] wl2))))
           in
        let uu____19914 = FStar_Util.physical_equality c1 c2  in
        if uu____19914
        then
          let uu____19915 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____19915
        else
          ((let uu____19918 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____19918
            then
              let uu____19919 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____19920 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____19919
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____19920
            else ());
           (let uu____19922 =
              let uu____19931 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____19934 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____19931, uu____19934)  in
            match uu____19922 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____19952),FStar_Syntax_Syntax.Total
                    (t2,uu____19954)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____19971 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____19971 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____19972,FStar_Syntax_Syntax.Total uu____19973) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____19991),FStar_Syntax_Syntax.Total
                    (t2,uu____19993)) ->
                     let uu____20010 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20010 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____20012),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20014)) ->
                     let uu____20031 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20031 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____20033),FStar_Syntax_Syntax.GTotal
                    (t2,uu____20035)) ->
                     let uu____20052 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____20052 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____20053,FStar_Syntax_Syntax.Comp uu____20054) ->
                     let uu____20063 =
                       let uu___202_20066 = problem  in
                       let uu____20069 =
                         let uu____20070 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20070
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___202_20066.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20069;
                         FStar_TypeChecker_Common.relation =
                           (uu___202_20066.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___202_20066.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___202_20066.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___202_20066.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___202_20066.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___202_20066.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___202_20066.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___202_20066.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20063 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____20071,FStar_Syntax_Syntax.Comp uu____20072) ->
                     let uu____20081 =
                       let uu___202_20084 = problem  in
                       let uu____20087 =
                         let uu____20088 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20088
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___202_20084.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____20087;
                         FStar_TypeChecker_Common.relation =
                           (uu___202_20084.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___202_20084.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___202_20084.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___202_20084.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___202_20084.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___202_20084.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___202_20084.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___202_20084.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20081 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20089,FStar_Syntax_Syntax.GTotal uu____20090) ->
                     let uu____20099 =
                       let uu___203_20102 = problem  in
                       let uu____20105 =
                         let uu____20106 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20106
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___203_20102.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___203_20102.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___203_20102.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20105;
                         FStar_TypeChecker_Common.element =
                           (uu___203_20102.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___203_20102.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___203_20102.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___203_20102.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___203_20102.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___203_20102.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20099 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20107,FStar_Syntax_Syntax.Total uu____20108) ->
                     let uu____20117 =
                       let uu___203_20120 = problem  in
                       let uu____20123 =
                         let uu____20124 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____20124
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___203_20120.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___203_20120.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___203_20120.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____20123;
                         FStar_TypeChecker_Common.element =
                           (uu___203_20120.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___203_20120.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___203_20120.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___203_20120.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___203_20120.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___203_20120.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____20117 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____20125,FStar_Syntax_Syntax.Comp uu____20126) ->
                     let uu____20127 =
                       (((FStar_Syntax_Util.is_ml_comp c11) &&
                           (FStar_Syntax_Util.is_ml_comp c21))
                          ||
                          ((FStar_Syntax_Util.is_total_comp c11) &&
                             (FStar_Syntax_Util.is_total_comp c21)))
                         ||
                         (((FStar_Syntax_Util.is_total_comp c11) &&
                             (FStar_Syntax_Util.is_ml_comp c21))
                            &&
                            (problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB))
                        in
                     if uu____20127
                     then
                       let uu____20128 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____20128 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____20132 =
                            let uu____20137 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____20137
                            then (c1_comp, c2_comp)
                            else
                              (let uu____20143 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____20144 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____20143, uu____20144))
                             in
                          match uu____20132 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11
                              in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21
                              in
                           (let uu____20151 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____20151
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____20153 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____20153 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____20156 =
                                  let uu____20157 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____20158 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____20157 uu____20158
                                   in
                                giveup env uu____20156 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____20165 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____20198  ->
              match uu____20198 with
              | (uu____20209,tm,uu____20211,uu____20212,uu____20213) ->
                  FStar_Syntax_Print.term_to_string tm))
       in
    FStar_All.pipe_right uu____20165 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____20246 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____20246 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____20264 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____20292  ->
                match uu____20292 with
                | (u1,u2) ->
                    let uu____20299 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____20300 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____20299 uu____20300))
         in
      FStar_All.pipe_right uu____20264 (FStar_String.concat ", ")  in
    FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1
  
let (guard_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun env  ->
    fun g  ->
      match ((g.FStar_TypeChecker_Env.guard_f),
              (g.FStar_TypeChecker_Env.deferred),
              (g.FStar_TypeChecker_Env.univ_ineqs))
      with
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____20327,[])) -> "{}"
      | uu____20352 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____20375 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____20375
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____20378 =
              FStar_List.map
                (fun uu____20388  ->
                   match uu____20388 with
                   | (uu____20393,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____20378 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____20398 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____20398 imps
  
let (new_t_problem :
  worklist ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
              FStar_Range.range ->
                (FStar_TypeChecker_Common.prob,worklist)
                  FStar_Pervasives_Native.tuple2)
  =
  fun wl  ->
    fun env  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun loc  ->
                let reason =
                  let uu____20451 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____20451
                  then
                    let uu____20452 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____20453 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____20452
                      (rel_to_string rel) uu____20453
                  else "TOP"  in
                let uu____20455 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____20455 with
                | (p,wl1) -> ((FStar_TypeChecker_Common.TProb p), wl1)
  
let (new_t_prob :
  worklist ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            (FStar_TypeChecker_Common.prob,FStar_Syntax_Syntax.bv,worklist)
              FStar_Pervasives_Native.tuple3)
  =
  fun wl  ->
    fun env  ->
      fun t1  ->
        fun rel  ->
          fun t2  ->
            let x =
              let uu____20512 =
                let uu____20515 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                  uu____20515
                 in
              FStar_Syntax_Syntax.new_bv uu____20512 t1  in
            let uu____20518 =
              let uu____20523 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____20523
               in
            match uu____20518 with | (p,wl1) -> (p, x, wl1)
  
let (solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob,Prims.string)
         FStar_Pervasives_Native.tuple2 ->
         (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
           FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
        ->
        (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun probs  ->
      fun err  ->
        let probs1 =
          let uu____20579 = FStar_Options.eager_inference ()  in
          if uu____20579
          then
            let uu___204_20580 = probs  in
            {
              attempting = (uu___204_20580.attempting);
              wl_deferred = (uu___204_20580.wl_deferred);
              ctr = (uu___204_20580.ctr);
              defer_ok = false;
              smt_ok = (uu___204_20580.smt_ok);
              tcenv = (uu___204_20580.tcenv);
              wl_implicits = (uu___204_20580.wl_implicits)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success (deferred,implicits) ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some (deferred, implicits))
        | Failed (d,s) ->
            ((let uu____20600 =
                (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "ExplainRel"))
                  ||
                  (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel"))
                 in
              if uu____20600
              then
                let uu____20601 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____20601
              else ());
             (let result = err (d, s)  in
              FStar_Syntax_Unionfind.rollback tx; result))
  
let (simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____20623 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____20623
            then
              let uu____20624 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____20624
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____20628 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____20628
             then
               let uu____20629 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____20629
             else ());
            (let f2 =
               let uu____20632 =
                 let uu____20633 = FStar_Syntax_Util.unmeta f1  in
                 uu____20633.FStar_Syntax_Syntax.n  in
               match uu____20632 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____20637 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___205_20638 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___205_20638.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___205_20638.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___205_20638.FStar_TypeChecker_Env.implicits)
             })))
  
let (with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.deferred,(Prims.string,FStar_Syntax_Syntax.term,
                                           FStar_Syntax_Syntax.ctx_uvar,
                                           FStar_Range.range,Prims.bool)
                                           FStar_Pervasives_Native.tuple5
                                           Prims.list)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred,implicits) ->
            let uu____20752 =
              let uu____20753 =
                let uu____20754 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_28  -> FStar_TypeChecker_Common.NonTrivial _0_28)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____20754;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____20753  in
            FStar_All.pipe_left
              (fun _0_29  -> FStar_Pervasives_Native.Some _0_29) uu____20752
  
let with_guard_no_simp :
  'Auu____20769 .
    'Auu____20769 ->
      FStar_TypeChecker_Common.prob ->
        FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some d ->
            let uu____20792 =
              let uu____20793 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_30  -> FStar_TypeChecker_Common.NonTrivial _0_30)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____20793;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____20792
  
let (try_teq :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun smt_ok  ->
    fun env  ->
      fun t1  ->
        fun t2  ->
          (let uu____20833 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____20833
           then
             let uu____20834 = FStar_Syntax_Print.term_to_string t1  in
             let uu____20835 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____20834
               uu____20835
           else ());
          (let uu____20837 =
             let uu____20842 = empty_worklist env  in
             let uu____20843 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem uu____20842 env t1 FStar_TypeChecker_Common.EQ t2
               FStar_Pervasives_Native.None uu____20843
              in
           match uu____20837 with
           | (prob,wl) ->
               let g =
                 let uu____20851 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____20871  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____20851  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____20915 = try_teq true env t1 t2  in
        match uu____20915 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____20919 = FStar_TypeChecker_Env.get_range env  in
              let uu____20920 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____20919 uu____20920);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____20927 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____20927
              then
                let uu____20928 = FStar_Syntax_Print.term_to_string t1  in
                let uu____20929 = FStar_Syntax_Print.term_to_string t2  in
                let uu____20930 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____20928
                  uu____20929 uu____20930
              else ());
             g)
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____20952 = FStar_TypeChecker_Env.get_range env  in
          let uu____20953 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____20952 uu____20953
  
let (sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let rel =
          if env.FStar_TypeChecker_Env.use_eq
          then FStar_TypeChecker_Common.EQ
          else FStar_TypeChecker_Common.SUB  in
        (let uu____20978 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____20978
         then
           let uu____20979 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____20980 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____20979 uu____20980
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____20983 =
           let uu____20990 = empty_worklist env  in
           let uu____20991 = FStar_TypeChecker_Env.get_range env  in
           new_problem uu____20990 env c1 rel c2 FStar_Pervasives_Native.None
             uu____20991 "sub_comp"
            in
         match uu____20983 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             let uu____21001 =
               solve_and_commit env (singleton wl prob1 true)
                 (fun uu____21021  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob1) uu____21001)
  
let (solve_universe_inequalities' :
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                                 FStar_Syntax_Syntax.universe)
                                                 FStar_Pervasives_Native.tuple2
                                                 Prims.list)
        FStar_Pervasives_Native.tuple2 -> unit)
  =
  fun tx  ->
    fun env  ->
      fun uu____21076  ->
        match uu____21076 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____21119 =
                 let uu____21124 =
                   let uu____21125 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____21126 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____21125 uu____21126
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____21124)  in
               let uu____21127 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____21119 uu____21127)
               in
            let equiv1 v1 v' =
              let uu____21139 =
                let uu____21144 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____21145 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____21144, uu____21145)  in
              match uu____21139 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____21164 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____21194 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____21194 with
                      | FStar_Syntax_Syntax.U_unif uu____21201 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____21230  ->
                                    match uu____21230 with
                                    | (u,v') ->
                                        let uu____21239 = equiv1 v1 v'  in
                                        if uu____21239
                                        then
                                          let uu____21242 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____21242 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____21258 -> []))
               in
            let uu____21263 =
              let wl =
                let uu___206_21267 = empty_worklist env  in
                {
                  attempting = (uu___206_21267.attempting);
                  wl_deferred = (uu___206_21267.wl_deferred);
                  ctr = (uu___206_21267.ctr);
                  defer_ok = false;
                  smt_ok = (uu___206_21267.smt_ok);
                  tcenv = (uu___206_21267.tcenv);
                  wl_implicits = (uu___206_21267.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____21285  ->
                      match uu____21285 with
                      | (lb,v1) ->
                          let uu____21292 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____21292 with
                           | USolved wl1 -> ()
                           | uu____21294 -> fail1 lb v1)))
               in
            let rec check_ineq uu____21304 =
              match uu____21304 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____21313) -> true
                   | (FStar_Syntax_Syntax.U_succ
                      u0,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name
                      u0,FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif
                      u0,FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Syntax_Unionfind.univ_equiv u0 v0
                   | (FStar_Syntax_Syntax.U_name
                      uu____21336,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____21338,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____21349) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____21356,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____21364 -> false)
               in
            let uu____21369 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____21384  ->
                      match uu____21384 with
                      | (u,v1) ->
                          let uu____21391 = check_ineq (u, v1)  in
                          if uu____21391
                          then true
                          else
                            ((let uu____21394 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____21394
                              then
                                let uu____21395 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____21396 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____21395
                                  uu____21396
                              else ());
                             false)))
               in
            if uu____21369
            then ()
            else
              ((let uu____21400 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____21400
                then
                  ((let uu____21402 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____21402);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____21412 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____21412))
                else ());
               (let uu____21422 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____21422))
  
let (solve_universe_inequalities :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                               FStar_Syntax_Syntax.universe)
                                               FStar_Pervasives_Native.tuple2
                                               Prims.list)
      FStar_Pervasives_Native.tuple2 -> unit)
  =
  fun env  ->
    fun ineqs  ->
      let tx = FStar_Syntax_Unionfind.new_transaction ()  in
      solve_universe_inequalities' tx env ineqs;
      FStar_Syntax_Unionfind.commit tx
  
let (try_solve_deferred_constraints :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun defer_ok  ->
    fun env  ->
      fun g  ->
        let fail1 uu____21489 =
          match uu____21489 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___207_21510 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___207_21510.attempting);
            wl_deferred = (uu___207_21510.wl_deferred);
            ctr = (uu___207_21510.ctr);
            defer_ok;
            smt_ok = (uu___207_21510.smt_ok);
            tcenv = (uu___207_21510.tcenv);
            wl_implicits = (uu___207_21510.wl_implicits)
          }  in
        (let uu____21512 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____21512
         then
           let uu____21513 = FStar_Util.string_of_bool defer_ok  in
           let uu____21514 = wl_to_string wl  in
           let uu____21515 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____21513 uu____21514 uu____21515
         else ());
        (let g1 =
           let uu____21528 = solve_and_commit env wl fail1  in
           match uu____21528 with
           | FStar_Pervasives_Native.Some
               (uu____21535::uu____21536,uu____21537) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___208_21562 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___208_21562.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___208_21562.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____21573 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___209_21581 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___209_21581.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___209_21581.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___209_21581.FStar_TypeChecker_Env.implicits)
          }))
  
let (solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints false env g 
let (solve_some_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints true env g 
let (last_proof_ns :
  FStar_TypeChecker_Env.proof_namespace FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (maybe_update_proof_ns : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let pns = env.FStar_TypeChecker_Env.proof_ns  in
    let uu____21629 = FStar_ST.op_Bang last_proof_ns  in
    match uu____21629 with
    | FStar_Pervasives_Native.None  ->
        FStar_ST.op_Colon_Equals last_proof_ns
          (FStar_Pervasives_Native.Some pns)
    | FStar_Pervasives_Native.Some old ->
        if old = pns
        then ()
        else
          ((env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
             ();
           FStar_ST.op_Colon_Equals last_proof_ns
             (FStar_Pervasives_Native.Some pns))
  
let (discharge_guard' :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Env.guard_t ->
        Prims.bool ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun use_env_range_msg  ->
    fun env  ->
      fun g  ->
        fun use_smt  ->
          let debug1 =
            ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel"))
               ||
               (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "SMTQuery")))
              ||
              (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Tac"))
             in
          let g1 = solve_deferred_constraints env g  in
          let ret_g =
            let uu___210_21752 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___210_21752.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___210_21752.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___210_21752.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____21753 =
            let uu____21754 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____21754  in
          if uu____21753
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____21762 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____21763 =
                       let uu____21764 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____21764
                        in
                     FStar_Errors.diag uu____21762 uu____21763)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____21768 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____21769 =
                        let uu____21770 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____21770
                         in
                      FStar_Errors.diag uu____21768 uu____21769)
                   else ();
                   (let uu____21773 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____21773 "discharge_guard'"
                      env vc1);
                   (let uu____21774 = check_trivial vc1  in
                    match uu____21774 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____21781 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____21782 =
                                let uu____21783 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____21783
                                 in
                              FStar_Errors.diag uu____21781 uu____21782)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____21788 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____21789 =
                                let uu____21790 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____21790
                                 in
                              FStar_Errors.diag uu____21788 uu____21789)
                           else ();
                           (let vcs =
                              let uu____21803 = FStar_Options.use_tactics ()
                                 in
                              if uu____21803
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____21825  ->
                                     (let uu____21827 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a238  -> ())
                                        uu____21827);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____21870  ->
                                              match uu____21870 with
                                              | (env1,goal,opts) ->
                                                  let uu____21886 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Normalize.Simplify;
                                                      FStar_TypeChecker_Normalize.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____21886, opts)))))
                              else
                                (let uu____21888 =
                                   let uu____21895 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____21895)  in
                                 [uu____21888])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____21932  ->
                                    match uu____21932 with
                                    | (env1,goal,opts) ->
                                        let uu____21948 = check_trivial goal
                                           in
                                        (match uu____21948 with
                                         | FStar_TypeChecker_Common.Trivial 
                                             ->
                                             if debug1
                                             then
                                               FStar_Util.print_string
                                                 "Goal completely solved by tactic\n"
                                             else ()
                                         | FStar_TypeChecker_Common.NonTrivial
                                             goal1 ->
                                             (FStar_Options.push ();
                                              FStar_Options.set opts;
                                              maybe_update_proof_ns env1;
                                              if debug1
                                              then
                                                (let uu____21956 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____21957 =
                                                   let uu____21958 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____21959 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____21958 uu____21959
                                                    in
                                                 FStar_Errors.diag
                                                   uu____21956 uu____21957)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____21962 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____21963 =
                                                   let uu____21964 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____21964
                                                    in
                                                 FStar_Errors.diag
                                                   uu____21962 uu____21963)
                                              else ();
                                              (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                use_env_range_msg env1 goal1;
                                              FStar_Options.pop ())))));
                           FStar_Pervasives_Native.Some ret_g)))))
  
let (discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____21978 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____21978 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____21985 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____21985
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____21996 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____21996 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let (resolve_implicits' :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      Prims.bool ->
        FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun must_total  ->
      fun forcelax  ->
        fun g  ->
          let unresolved u =
            let uu____22029 = FStar_Syntax_Util.head_and_args u  in
            match uu____22029 with
            | (hd1,uu____22045) ->
                let uu____22066 =
                  let uu____22067 = FStar_Syntax_Subst.compress u  in
                  uu____22067.FStar_Syntax_Syntax.n  in
                (match uu____22066 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____22070 -> true
                 | uu____22077 -> false)
             in
          let rec until_fixpoint acc implicits =
            let uu____22097 = acc  in
            match uu____22097 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____22159 = hd1  in
                     (match uu____22159 with
                      | (reason,tm,ctx_u,r,should_check) ->
                          if Prims.op_Negation should_check
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____22176 = unresolved tm  in
                             if uu____22176
                             then until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               (let env1 =
                                  let uu___211_22189 = env  in
                                  {
                                    FStar_TypeChecker_Env.solver =
                                      (uu___211_22189.FStar_TypeChecker_Env.solver);
                                    FStar_TypeChecker_Env.range =
                                      (uu___211_22189.FStar_TypeChecker_Env.range);
                                    FStar_TypeChecker_Env.curmodule =
                                      (uu___211_22189.FStar_TypeChecker_Env.curmodule);
                                    FStar_TypeChecker_Env.gamma =
                                      (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                    FStar_TypeChecker_Env.gamma_sig =
                                      (uu___211_22189.FStar_TypeChecker_Env.gamma_sig);
                                    FStar_TypeChecker_Env.gamma_cache =
                                      (uu___211_22189.FStar_TypeChecker_Env.gamma_cache);
                                    FStar_TypeChecker_Env.modules =
                                      (uu___211_22189.FStar_TypeChecker_Env.modules);
                                    FStar_TypeChecker_Env.expected_typ =
                                      (uu___211_22189.FStar_TypeChecker_Env.expected_typ);
                                    FStar_TypeChecker_Env.sigtab =
                                      (uu___211_22189.FStar_TypeChecker_Env.sigtab);
                                    FStar_TypeChecker_Env.is_pattern =
                                      (uu___211_22189.FStar_TypeChecker_Env.is_pattern);
                                    FStar_TypeChecker_Env.instantiate_imp =
                                      (uu___211_22189.FStar_TypeChecker_Env.instantiate_imp);
                                    FStar_TypeChecker_Env.effects =
                                      (uu___211_22189.FStar_TypeChecker_Env.effects);
                                    FStar_TypeChecker_Env.generalize =
                                      (uu___211_22189.FStar_TypeChecker_Env.generalize);
                                    FStar_TypeChecker_Env.letrecs =
                                      (uu___211_22189.FStar_TypeChecker_Env.letrecs);
                                    FStar_TypeChecker_Env.top_level =
                                      (uu___211_22189.FStar_TypeChecker_Env.top_level);
                                    FStar_TypeChecker_Env.check_uvars =
                                      (uu___211_22189.FStar_TypeChecker_Env.check_uvars);
                                    FStar_TypeChecker_Env.use_eq =
                                      (uu___211_22189.FStar_TypeChecker_Env.use_eq);
                                    FStar_TypeChecker_Env.is_iface =
                                      (uu___211_22189.FStar_TypeChecker_Env.is_iface);
                                    FStar_TypeChecker_Env.admit =
                                      (uu___211_22189.FStar_TypeChecker_Env.admit);
                                    FStar_TypeChecker_Env.lax =
                                      (uu___211_22189.FStar_TypeChecker_Env.lax);
                                    FStar_TypeChecker_Env.lax_universes =
                                      (uu___211_22189.FStar_TypeChecker_Env.lax_universes);
                                    FStar_TypeChecker_Env.failhard =
                                      (uu___211_22189.FStar_TypeChecker_Env.failhard);
                                    FStar_TypeChecker_Env.nosynth =
                                      (uu___211_22189.FStar_TypeChecker_Env.nosynth);
                                    FStar_TypeChecker_Env.tc_term =
                                      (uu___211_22189.FStar_TypeChecker_Env.tc_term);
                                    FStar_TypeChecker_Env.type_of =
                                      (uu___211_22189.FStar_TypeChecker_Env.type_of);
                                    FStar_TypeChecker_Env.universe_of =
                                      (uu___211_22189.FStar_TypeChecker_Env.universe_of);
                                    FStar_TypeChecker_Env.check_type_of =
                                      (uu___211_22189.FStar_TypeChecker_Env.check_type_of);
                                    FStar_TypeChecker_Env.use_bv_sorts =
                                      (uu___211_22189.FStar_TypeChecker_Env.use_bv_sorts);
                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                      =
                                      (uu___211_22189.FStar_TypeChecker_Env.qtbl_name_and_index);
                                    FStar_TypeChecker_Env.normalized_eff_names
                                      =
                                      (uu___211_22189.FStar_TypeChecker_Env.normalized_eff_names);
                                    FStar_TypeChecker_Env.proof_ns =
                                      (uu___211_22189.FStar_TypeChecker_Env.proof_ns);
                                    FStar_TypeChecker_Env.synth_hook =
                                      (uu___211_22189.FStar_TypeChecker_Env.synth_hook);
                                    FStar_TypeChecker_Env.splice =
                                      (uu___211_22189.FStar_TypeChecker_Env.splice);
                                    FStar_TypeChecker_Env.is_native_tactic =
                                      (uu___211_22189.FStar_TypeChecker_Env.is_native_tactic);
                                    FStar_TypeChecker_Env.identifier_info =
                                      (uu___211_22189.FStar_TypeChecker_Env.identifier_info);
                                    FStar_TypeChecker_Env.tc_hooks =
                                      (uu___211_22189.FStar_TypeChecker_Env.tc_hooks);
                                    FStar_TypeChecker_Env.dsenv =
                                      (uu___211_22189.FStar_TypeChecker_Env.dsenv);
                                    FStar_TypeChecker_Env.dep_graph =
                                      (uu___211_22189.FStar_TypeChecker_Env.dep_graph)
                                  }  in
                                let tm1 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    tm
                                   in
                                let env2 =
                                  if forcelax
                                  then
                                    let uu___212_22192 = env1  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___212_22192.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___212_22192.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___212_22192.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___212_22192.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___212_22192.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___212_22192.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___212_22192.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___212_22192.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___212_22192.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___212_22192.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___212_22192.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___212_22192.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___212_22192.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___212_22192.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___212_22192.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___212_22192.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___212_22192.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___212_22192.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___212_22192.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___212_22192.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___212_22192.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___212_22192.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___212_22192.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___212_22192.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___212_22192.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___212_22192.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___212_22192.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___212_22192.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___212_22192.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___212_22192.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___212_22192.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___212_22192.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___212_22192.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___212_22192.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___212_22192.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___212_22192.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___212_22192.FStar_TypeChecker_Env.dep_graph)
                                    }
                                  else env1  in
                                (let uu____22195 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____22195
                                 then
                                   let uu____22196 =
                                     FStar_Syntax_Print.uvar_to_string
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                      in
                                   let uu____22197 =
                                     FStar_Syntax_Print.term_to_string tm1
                                      in
                                   let uu____22198 =
                                     FStar_Syntax_Print.term_to_string
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                      in
                                   let uu____22199 =
                                     FStar_Range.string_of_range r  in
                                   FStar_Util.print5
                                     "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                     uu____22196 uu____22197 uu____22198
                                     reason uu____22199
                                 else ());
                                (let g1 =
                                   try
                                     env2.FStar_TypeChecker_Env.check_type_of
                                       must_total env2 tm1
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                   with
                                   | e when FStar_Errors.handleable e ->
                                       ((let uu____22210 =
                                           let uu____22219 =
                                             let uu____22226 =
                                               let uu____22227 =
                                                 FStar_Syntax_Print.uvar_to_string
                                                   ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                  in
                                               let uu____22228 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env2 tm1
                                                  in
                                               FStar_Util.format2
                                                 "Failed while checking implicit %s set to %s"
                                                 uu____22227 uu____22228
                                                in
                                             (FStar_Errors.Error_BadImplicit,
                                               uu____22226, r)
                                              in
                                           [uu____22219]  in
                                         FStar_Errors.add_errors uu____22210);
                                        FStar_Exn.raise e)
                                    in
                                 let g2 =
                                   if env2.FStar_TypeChecker_Env.is_pattern
                                   then
                                     let uu___215_22242 = g1  in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___215_22242.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___215_22242.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___215_22242.FStar_TypeChecker_Env.implicits)
                                     }
                                   else g1  in
                                 let g' =
                                   let uu____22245 =
                                     discharge_guard'
                                       (FStar_Pervasives_Native.Some
                                          (fun uu____22252  ->
                                             FStar_Syntax_Print.term_to_string
                                               tm1)) env2 g2 true
                                      in
                                   match uu____22245 with
                                   | FStar_Pervasives_Native.Some g3 -> g3
                                   | FStar_Pervasives_Native.None  ->
                                       failwith
                                         "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                                    in
                                 until_fixpoint
                                   ((FStar_List.append
                                       g'.FStar_TypeChecker_Env.implicits out),
                                     true) tl1)))))
             in
          let uu___216_22264 = g  in
          let uu____22265 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___216_22264.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___216_22264.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___216_22264.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____22265
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> resolve_implicits' env true false g 
let (resolve_implicits_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> resolve_implicits' env false true g 
let (force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> unit) =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____22319 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____22319 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____22330 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a239  -> ()) uu____22330
      | (reason,e,ctx_u,r,should_check)::uu____22336 ->
          let uu____22359 =
            let uu____22364 =
              let uu____22365 =
                FStar_Syntax_Print.uvar_to_string
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____22366 =
                FStar_TypeChecker_Normalize.term_to_string env
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              let uu____22367 = FStar_Util.string_of_bool should_check  in
              FStar_Util.format4
                "Failed to resolve implicit argument %s of type %s introduced for %s (should check=%s)"
                uu____22365 uu____22366 reason uu____22367
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____22364)
             in
          FStar_Errors.raise_error uu____22359 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___217_22378 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___217_22378.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___217_22378.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___217_22378.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____22393 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____22393 with
      | FStar_Pervasives_Native.Some uu____22399 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22415 = try_teq false env t1 t2  in
        match uu____22415 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> discharge_guard_nosmt env g
  
let (check_subtyping :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____22449 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22449
         then
           let uu____22450 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____22451 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____22450
             uu____22451
         else ());
        (let uu____22453 =
           let uu____22460 = empty_worklist env  in
           new_t_prob uu____22460 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____22453 with
         | (prob,x,wl) ->
             let g =
               let uu____22473 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____22493  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____22473  in
             ((let uu____22523 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____22523
               then
                 let uu____22524 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____22525 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____22526 =
                   let uu____22527 = FStar_Util.must g  in
                   guard_to_string env uu____22527  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____22524 uu____22525 uu____22526
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   FStar_Pervasives_Native.Some (x, g1))))
  
let (get_subtyping_predicate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22561 = check_subtyping env t1 t2  in
        match uu____22561 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____22580 =
              let uu____22581 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____22581 g  in
            FStar_Pervasives_Native.Some uu____22580
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____22599 = check_subtyping env t1 t2  in
        match uu____22599 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____22618 =
              let uu____22619 =
                let uu____22620 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____22620]  in
              close_guard env uu____22619 g  in
            FStar_Pervasives_Native.Some uu____22618
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____22649 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____22649
         then
           let uu____22650 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____22651 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____22650
             uu____22651
         else ());
        (let uu____22653 =
           let uu____22660 = empty_worklist env  in
           new_t_prob uu____22660 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____22653 with
         | (prob,x,wl) ->
             let g =
               let uu____22667 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____22687  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____22667  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____22718 =
                      let uu____22719 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____22719]  in
                    close_guard env uu____22718 g1  in
                  discharge_guard_nosmt env g2))
  