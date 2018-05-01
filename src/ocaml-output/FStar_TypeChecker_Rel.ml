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
          let uu___118_102 = g  in
          {
            FStar_TypeChecker_Env.guard_f =
              (FStar_TypeChecker_Common.NonTrivial f');
            FStar_TypeChecker_Env.deferred =
              (uu___118_102.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___118_102.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___118_102.FStar_TypeChecker_Env.implicits)
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
          let uu___119_248 = g  in
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
              (uu___119_248.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___119_248.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___119_248.FStar_TypeChecker_Env.implicits)
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
          let uu___120_331 = g  in
          let uu____332 =
            let uu____333 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____333  in
          {
            FStar_TypeChecker_Env.guard_f = uu____332;
            FStar_TypeChecker_Env.deferred =
              (uu___120_331.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___120_331.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___120_331.FStar_TypeChecker_Env.implicits)
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
            let uu___121_499 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___121_499.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___121_499.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___121_499.FStar_TypeChecker_Env.implicits)
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
            let uu___122_559 = g  in
            let uu____560 =
              let uu____561 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____561  in
            {
              FStar_TypeChecker_Env.guard_f = uu____560;
              FStar_TypeChecker_Env.deferred =
                (uu___122_559.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___122_559.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___122_559.FStar_TypeChecker_Env.implicits)
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
                  should_check gamma binders;
                (let t =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_uvar ctx_uvar)
                     FStar_Pervasives_Native.None r
                    in
                 (ctx_uvar, t,
                   (let uu___123_923 = wl  in
                    {
                      attempting = (uu___123_923.attempting);
                      wl_deferred = (uu___123_923.wl_deferred);
                      ctr = (uu___123_923.ctr);
                      defer_ok = (uu___123_923.defer_ok);
                      smt_ok = (uu___123_923.smt_ok);
                      tcenv = (uu___123_923.tcenv);
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
    match projectee with | Success _0 -> true | uu____987 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred,FStar_TypeChecker_Env.implicits)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____1017 -> false
  
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
    match projectee with | COVARIANT  -> true | uu____1042 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____1048 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____1054 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
[@@deriving show]
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
[@@deriving show]
type 'a problem_t = 'a FStar_TypeChecker_Common.problem[@@deriving show]
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___89_1069  ->
    match uu___89_1069 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____1075 =
      let uu____1076 = FStar_Syntax_Subst.compress t  in
      uu____1076.FStar_Syntax_Syntax.n  in
    match uu____1075 with
    | FStar_Syntax_Syntax.Tm_uvar u -> print_ctx_uvar u
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar u;
           FStar_Syntax_Syntax.pos = uu____1081;
           FStar_Syntax_Syntax.vars = uu____1082;_},args)
        ->
        let uu____1104 = print_ctx_uvar u  in
        let uu____1105 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____1104 uu____1105
    | uu____1106 -> FStar_Syntax_Print.term_to_string t
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___90_1116  ->
      match uu___90_1116 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1120 =
            let uu____1123 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____1124 =
              let uu____1127 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____1128 =
                let uu____1131 =
                  let uu____1134 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____1134]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____1131
                 in
              uu____1127 :: uu____1128  in
            uu____1123 :: uu____1124  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s" uu____1120
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1138 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____1139 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____1140 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____1138 uu____1139
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1140
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___91_1150  ->
      match uu___91_1150 with
      | UNIV (u,t) ->
          let x =
            let uu____1154 = FStar_Options.hide_uvar_nums ()  in
            if uu____1154
            then "?"
            else
              (let uu____1156 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____1156 FStar_Util.string_of_int)
             in
          let uu____1157 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____1157
      | TERM (u,t) ->
          let x =
            let uu____1161 = FStar_Options.hide_uvar_nums ()  in
            if uu____1161
            then "?"
            else
              (let uu____1163 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____1163 FStar_Util.string_of_int)
             in
          let uu____1164 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____1164
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____1179 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____1179 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1193 =
      let uu____1196 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1196
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1193 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1209 .
    (FStar_Syntax_Syntax.term,'Auu____1209) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1227 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1245  ->
              match uu____1245 with
              | (x,uu____1251) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1227 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
    let uu____1259 =
      let uu____1260 = FStar_Options.eager_inference ()  in
      Prims.op_Negation uu____1260  in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____1259;
      smt_ok = true;
      tcenv = env;
      wl_implicits = []
    }
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___124_1292 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___124_1292.wl_deferred);
          ctr = (uu___124_1292.ctr);
          defer_ok = (uu___124_1292.defer_ok);
          smt_ok;
          tcenv = (uu___124_1292.tcenv);
          wl_implicits = (uu___124_1292.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1299 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1299,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2 Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___125_1322 = empty_worklist env  in
      let uu____1323 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1323;
        wl_deferred = (uu___125_1322.wl_deferred);
        ctr = (uu___125_1322.ctr);
        defer_ok = (uu___125_1322.defer_ok);
        smt_ok = (uu___125_1322.smt_ok);
        tcenv = (uu___125_1322.tcenv);
        wl_implicits = (uu___125_1322.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___126_1343 = wl  in
        {
          attempting = (uu___126_1343.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___126_1343.ctr);
          defer_ok = (uu___126_1343.defer_ok);
          smt_ok = (uu___126_1343.smt_ok);
          tcenv = (uu___126_1343.tcenv);
          wl_implicits = (uu___126_1343.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      let uu___127_1364 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___127_1364.wl_deferred);
        ctr = (uu___127_1364.ctr);
        defer_ok = (uu___127_1364.defer_ok);
        smt_ok = (uu___127_1364.smt_ok);
        tcenv = (uu___127_1364.tcenv);
        wl_implicits = (uu___127_1364.wl_implicits)
      }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1381 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1381
         then
           let uu____1382 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____1382
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___92_1388  ->
    match uu___92_1388 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1393 .
    'Auu____1393 FStar_TypeChecker_Common.problem ->
      'Auu____1393 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___128_1405 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___128_1405.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___128_1405.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___128_1405.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___128_1405.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___128_1405.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___128_1405.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___128_1405.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1412 .
    'Auu____1412 FStar_TypeChecker_Common.problem ->
      'Auu____1412 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___93_1429  ->
    match uu___93_1429 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_18  -> FStar_TypeChecker_Common.TProb _0_18)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_19  -> FStar_TypeChecker_Common.CProb _0_19)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___94_1444  ->
    match uu___94_1444 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___129_1450 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___129_1450.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___129_1450.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___129_1450.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___129_1450.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___129_1450.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___129_1450.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___129_1450.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___129_1450.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___129_1450.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___130_1458 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___130_1458.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___130_1458.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___130_1458.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___130_1458.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___130_1458.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___130_1458.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___130_1458.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___130_1458.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___130_1458.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___95_1470  ->
      match uu___95_1470 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___96_1475  ->
    match uu___96_1475 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___97_1486  ->
    match uu___97_1486 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___98_1499  ->
    match uu___98_1499 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___99_1512  ->
    match uu___99_1512 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___100_1523  ->
    match uu___100_1523 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.ctx_uvar)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___101_1538  ->
    match uu___101_1538 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1557 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv,'Auu____1557) FStar_Pervasives_Native.tuple2
          Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1585 =
          let uu____1586 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1586  in
        if uu____1585
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1620)::bs ->
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
        let uu____1687 =
          let uu____1688 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1688  in
        if uu____1687
        then ()
        else
          (let uu____1690 =
             let uu____1693 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1693
              in
           def_check_closed_in (p_loc prob) msg uu____1690 phi)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      (let uu____1723 =
         let uu____1724 = FStar_Options.defensive ()  in
         Prims.op_Negation uu____1724  in
       if uu____1723
       then ()
       else
         (let uu____1726 = p_scope prob  in
          def_scope_wf (Prims.strcat msg ".scope") (p_loc prob) uu____1726));
      def_check_scoped (Prims.strcat msg ".guard") prob (p_guard prob);
      (match prob with
       | FStar_TypeChecker_Common.TProb p ->
           (def_check_scoped (Prims.strcat msg ".lhs") prob
              p.FStar_TypeChecker_Common.lhs;
            def_check_scoped (Prims.strcat msg ".rhs") prob
              p.FStar_TypeChecker_Common.rhs)
       | uu____1738 -> ())
  
let mk_eq2 :
  'Auu____1750 .
    worklist ->
      'Auu____1750 ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.term,worklist)
              FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun prob  ->
      fun t1  ->
        fun t2  ->
          let uu____1779 = FStar_Syntax_Util.type_u ()  in
          match uu____1779 with
          | (t_type,u) ->
              let uu____1790 =
                new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                  (wl.tcenv).FStar_TypeChecker_Env.gamma [] t_type false
                 in
              (match uu____1790 with
               | (uu____1805,tt,wl1) ->
                   let uu____1808 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                   (uu____1808, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___102_1813  ->
    match uu___102_1813 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_20  -> FStar_TypeChecker_Common.TProb _0_20) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_21  -> FStar_TypeChecker_Common.CProb _0_21) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____1829 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____1829 = (Prims.parse_int "1")
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1841  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____1939 .
    worklist ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____1939 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____1939 ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____1939 FStar_TypeChecker_Common.problem,worklist)
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
                    let uu____2005 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_Syntax_Util.arrow scope uu____2005  in
                  let uu____2008 =
                    let uu____2015 =
                      FStar_TypeChecker_Env.all_binders wl.tcenv  in
                    new_uvar
                      (Prims.strcat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange
                      (wl.tcenv).FStar_TypeChecker_Env.gamma uu____2015
                      guard_ty false
                     in
                  match uu____2008 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match scope with
                        | [] -> lg
                        | uu____2036 ->
                            let uu____2043 =
                              let uu____2048 =
                                FStar_List.map
                                  (fun uu____2061  ->
                                     match uu____2061 with
                                     | (x,i) ->
                                         let uu____2072 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         (uu____2072, i)) scope
                                 in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2048  in
                            uu____2043 FStar_Pervasives_Native.None
                              lg.FStar_Syntax_Syntax.pos
                         in
                      let uu____2075 =
                        let uu____2078 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2078;
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
                      (uu____2075, wl1)
  
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
                  let uu____2141 =
                    mk_problem wl scope orig lhs rel rhs elt reason  in
                  match uu____2141 with
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
                  let uu____2218 =
                    mk_problem wl scope orig lhs rel rhs elt reason  in
                  match uu____2218 with
                  | (p,wl1) -> ((FStar_TypeChecker_Common.CProb p), wl1)
  
let new_problem :
  'Auu____2253 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2253 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2253 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2253 FStar_TypeChecker_Common.problem,worklist)
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
                  let scope = FStar_TypeChecker_Env.all_binders env  in
                  let uu____2305 =
                    match subject with
                    | FStar_Pervasives_Native.None  ->
                        ([], FStar_Syntax_Util.ktype0,
                          FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some x ->
                        let bs =
                          let uu____2360 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2360]  in
                        let uu____2373 =
                          let uu____2376 =
                            FStar_Syntax_Syntax.mk_Total
                              FStar_Syntax_Util.ktype0
                             in
                          FStar_Syntax_Util.arrow bs uu____2376  in
                        let uu____2379 =
                          let uu____2382 = FStar_Syntax_Syntax.bv_to_name x
                             in
                          FStar_Pervasives_Native.Some uu____2382  in
                        (bs, uu____2373, uu____2379)
                     in
                  match uu____2305 with
                  | (bs,lg_ty,elt) ->
                      let uu____2422 =
                        new_uvar
                          (Prims.strcat "new_problem: logical guard for "
                             reason)
                          (let uu___131_2430 = wl  in
                           {
                             attempting = (uu___131_2430.attempting);
                             wl_deferred = (uu___131_2430.wl_deferred);
                             ctr = (uu___131_2430.ctr);
                             defer_ok = (uu___131_2430.defer_ok);
                             smt_ok = (uu___131_2430.smt_ok);
                             tcenv = env;
                             wl_implicits = (uu___131_2430.wl_implicits)
                           }) loc env.FStar_TypeChecker_Env.gamma scope lg_ty
                          false
                         in
                      (match uu____2422 with
                       | (ctx_uvar,lg,wl1) ->
                           let lg1 =
                             match elt with
                             | FStar_Pervasives_Native.None  -> lg
                             | FStar_Pervasives_Native.Some x ->
                                 let uu____2442 =
                                   let uu____2447 =
                                     let uu____2448 =
                                       FStar_Syntax_Syntax.as_arg x  in
                                     [uu____2448]  in
                                   FStar_Syntax_Syntax.mk_Tm_app lg
                                     uu____2447
                                    in
                                 uu____2442 FStar_Pervasives_Native.None loc
                              in
                           let uu____2469 =
                             let uu____2472 = next_pid ()  in
                             {
                               FStar_TypeChecker_Common.pid = uu____2472;
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
                           (uu____2469, wl1))
  
let problem_using_guard :
  'Auu____2489 .
    FStar_TypeChecker_Common.prob ->
      'Auu____2489 ->
        FStar_TypeChecker_Common.rel ->
          'Auu____2489 ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
              Prims.string -> 'Auu____2489 FStar_TypeChecker_Common.problem
  =
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let uu____2526 = next_pid ()  in
              {
                FStar_TypeChecker_Common.pid = uu____2526;
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
  'Auu____2537 .
    worklist ->
      'Auu____2537 FStar_TypeChecker_Common.problem ->
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
        let uu____2587 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel")
           in
        if uu____2587
        then
          let uu____2588 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2589 = prob_to_string env d  in
          let uu____2590 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2588 uu____2589 uu____2590 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2596 -> failwith "impossible"  in
           let uu____2597 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____2609 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2610 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2609, uu____2610)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____2614 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____2615 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____2614, uu____2615)
              in
           match uu____2597 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___103_2633  ->
            match uu___103_2633 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2645 -> FStar_Syntax_Unionfind.univ_change u t)
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
        (fun uu___104_2667  ->
           match uu___104_2667 with
           | UNIV uu____2670 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2677 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2677
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
        (fun uu___105_2701  ->
           match uu___105_2701 with
           | UNIV (u',t) ->
               let uu____2706 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2706
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2710 -> FStar_Pervasives_Native.None)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2721 =
        let uu____2722 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF] env uu____2722
         in
      FStar_Syntax_Subst.compress uu____2721
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2733 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____2733
  
let norm_arg :
  'Auu____2740 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term,'Auu____2740) FStar_Pervasives_Native.tuple2
        ->
        (FStar_Syntax_Syntax.term,'Auu____2740)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t  ->
      let uu____2763 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____2763, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____2804  ->
              match uu____2804 with
              | (x,imp) ->
                  let uu____2815 =
                    let uu___132_2816 = x  in
                    let uu____2817 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___132_2816.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___132_2816.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____2817
                    }  in
                  (uu____2815, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____2838 = aux u3  in FStar_Syntax_Syntax.U_succ uu____2838
        | FStar_Syntax_Syntax.U_max us ->
            let uu____2842 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____2842
        | uu____2845 -> u2  in
      let uu____2846 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____2846
  
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
                FStar_Syntax_Syntax.Delta_constant]
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
                (let uu____2960 = norm_refinement env t12  in
                 match uu____2960 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____2975;
                     FStar_Syntax_Syntax.vars = uu____2976;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3002 =
                       let uu____3003 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3004 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3003 uu____3004
                        in
                     failwith uu____3002)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3018 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3018
          | FStar_Syntax_Syntax.Tm_uinst uu____3019 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3054 =
                   let uu____3055 = FStar_Syntax_Subst.compress t1'  in
                   uu____3055.FStar_Syntax_Syntax.n  in
                 match uu____3054 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3070 -> aux true t1'
                 | uu____3077 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3092 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3121 =
                   let uu____3122 = FStar_Syntax_Subst.compress t1'  in
                   uu____3122.FStar_Syntax_Syntax.n  in
                 match uu____3121 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3137 -> aux true t1'
                 | uu____3144 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3159 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3202 =
                   let uu____3203 = FStar_Syntax_Subst.compress t1'  in
                   uu____3203.FStar_Syntax_Syntax.n  in
                 match uu____3202 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3218 -> aux true t1'
                 | uu____3225 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3240 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3255 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3270 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3285 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3300 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3327 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3358 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3379 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3394 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3421 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3458 ->
              let uu____3465 =
                let uu____3466 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3467 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3466 uu____3467
                 in
              failwith uu____3465
          | FStar_Syntax_Syntax.Tm_ascribed uu____3480 ->
              let uu____3507 =
                let uu____3508 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3509 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3508 uu____3509
                 in
              failwith uu____3507
          | FStar_Syntax_Syntax.Tm_delayed uu____3522 ->
              let uu____3547 =
                let uu____3548 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3549 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3548 uu____3549
                 in
              failwith uu____3547
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____3562 =
                let uu____3563 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3564 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3563 uu____3564
                 in
              failwith uu____3562
           in
        let uu____3577 = whnf env t1  in aux false uu____3577
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
                                  FStar_Pervasives_Native.tuple2
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let normalize_refinement :
  'Auu____3608 .
    FStar_TypeChecker_Normalize.steps ->
      FStar_TypeChecker_Env.env ->
        'Auu____3608 -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
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
      let uu____3639 = base_and_refinement env t  in
      FStar_All.pipe_right uu____3639 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let uu____3675 = FStar_Syntax_Syntax.null_bv t  in
    (uu____3675, FStar_Syntax_Util.t_true)
  
let as_refinement :
  'Auu____3686 .
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        'Auu____3686 ->
          FStar_Syntax_Syntax.term ->
            (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple2
  =
  fun delta1  ->
    fun env  ->
      fun wl  ->
        fun t  ->
          let uu____3711 = base_and_refinement_maybe_delta delta1 env t  in
          match uu____3711 with
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
  fun uu____3788  ->
    match uu____3788 with
    | (t_base,refopt) ->
        let uu____3821 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____3821 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____3861 =
      let uu____3864 =
        let uu____3867 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____3890  ->
                  match uu____3890 with | (uu____3897,uu____3898,x) -> x))
           in
        FStar_List.append wl.attempting uu____3867  in
      FStar_List.map (wl_prob_to_string wl) uu____3864  in
    FStar_All.pipe_right uu____3861 (FStar_String.concat "\n\t")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____3917 =
          let uu____3930 =
            let uu____3931 = FStar_Syntax_Subst.compress k  in
            uu____3931.FStar_Syntax_Syntax.n  in
          match uu____3930 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____3984 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____3984)
              else
                (let uu____3998 = FStar_Syntax_Util.abs_formals t  in
                 match uu____3998 with
                 | (ys',t1,uu____4021) ->
                     let uu____4026 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____4026))
          | uu____4067 ->
              let uu____4068 =
                let uu____4079 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____4079)  in
              ((ys, t), uu____4068)
           in
        match uu____3917 with
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
                 let uu____4128 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____4128 c  in
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
             let uu____4181 = p_guard_uvar prob  in
             match uu____4181 with
             | (xs,uv) ->
                 ((let uu____4189 =
                     FStar_Syntax_Unionfind.find
                       uv.FStar_Syntax_Syntax.ctx_uvar_head
                      in
                   match uu____4189 with
                   | FStar_Pervasives_Native.None  ->
                       ((let uu____4193 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug wl.tcenv)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____4193
                         then
                           let uu____4194 =
                             FStar_Util.string_of_int (p_pid prob)  in
                           let uu____4195 = print_ctx_uvar uv  in
                           let uu____4196 =
                             FStar_Syntax_Print.term_to_string phi  in
                           FStar_Util.print3
                             "Solving %s (%s) with formula %s\n" uu____4194
                             uu____4195 uu____4196
                         else ());
                        (let phi1 =
                           FStar_Syntax_Util.abs xs phi
                             (FStar_Pervasives_Native.Some
                                (FStar_Syntax_Util.residual_tot
                                   FStar_Syntax_Util.ktype0))
                            in
                         def_check_closed (p_loc prob) "solve_prob'" phi1;
                         FStar_Syntax_Util.set_uvar
                           uv.FStar_Syntax_Syntax.ctx_uvar_head phi1))
                   | FStar_Pervasives_Native.Some uu____4202 ->
                       if Prims.op_Negation resolve_ok
                       then
                         failwith
                           "Impossible: this instance has already been assigned a solution"
                       else ());
                  commit uvis;
                  (let uu___133_4205 = wl  in
                   {
                     attempting = (uu___133_4205.attempting);
                     wl_deferred = (uu___133_4205.wl_deferred);
                     ctr = (wl.ctr + (Prims.parse_int "1"));
                     defer_ok = (uu___133_4205.defer_ok);
                     smt_ok = (uu___133_4205.smt_ok);
                     tcenv = (uu___133_4205.tcenv);
                     wl_implicits = (uu___133_4205.wl_implicits)
                   })))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____4226 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck")
            in
         if uu____4226
         then
           let uu____4227 = FStar_Util.string_of_int pid  in
           let uu____4228 =
             let uu____4229 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____4229 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____4227 uu____4228
         else ());
        commit sol;
        (let uu___134_4236 = wl  in
         {
           attempting = (uu___134_4236.attempting);
           wl_deferred = (uu___134_4236.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___134_4236.defer_ok);
           smt_ok = (uu___134_4236.smt_ok);
           tcenv = (uu___134_4236.tcenv);
           wl_implicits = (uu___134_4236.wl_implicits)
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
             | (uu____4298,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____4324 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____4324
              in
           (let uu____4330 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "RelCheck")
               in
            if uu____4330
            then
              let uu____4331 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____4332 =
                let uu____4333 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____4333 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____4331 uu____4332
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
        let uu____4358 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____4358 FStar_Util.set_elements  in
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
      let uu____4392 = occurs uk t  in
      match uu____4392 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____4421 =
                 let uu____4422 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____4423 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____4422 uu____4423
                  in
               FStar_Pervasives_Native.Some uu____4421)
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
            let uu____4512 = maximal_prefix bs_tail bs'_tail  in
            (match uu____4512 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____4556 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____4604  ->
             match uu____4604 with
             | (x,uu____4614) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____4627 = FStar_List.last bs  in
      match uu____4627 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____4645) ->
          let uu____4650 =
            FStar_Util.prefix_until
              (fun uu___106_4665  ->
                 match uu___106_4665 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____4667 -> false) g
             in
          (match uu____4650 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____4680,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____4716 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____4716 with
        | (pfx,uu____4726) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____4738 =
              new_uvar src.FStar_Syntax_Syntax.ctx_uvar_reason wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
               in
            (match uu____4738 with
             | (uu____4745,src',wl1) ->
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
      let uu____4825 =
        FStar_All.pipe_right v2
          (FStar_List.fold_left
             (fun uu____4879  ->
                fun uu____4880  ->
                  match (uu____4879, uu____4880) with
                  | ((isect,isect_set),(x,imp)) ->
                      let uu____4961 =
                        let uu____4962 = FStar_Util.set_mem x v1_set  in
                        FStar_All.pipe_left Prims.op_Negation uu____4962  in
                      if uu____4961
                      then (isect, isect_set)
                      else
                        (let fvs =
                           FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort
                            in
                         let uu____4987 =
                           FStar_Util.set_is_subset_of fvs isect_set  in
                         if uu____4987
                         then
                           let uu____5000 = FStar_Util.set_add x isect_set
                              in
                           (((x, imp) :: isect), uu____5000)
                         else (isect, isect_set)))
             ([], FStar_Syntax_Syntax.no_names))
         in
      match uu____4825 with | (isect,uu____5037) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____5066 'Auu____5067 .
    (FStar_Syntax_Syntax.bv,'Auu____5066) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Syntax_Syntax.bv,'Auu____5067) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____5124  ->
              fun uu____5125  ->
                match (uu____5124, uu____5125) with
                | ((a,uu____5143),(b,uu____5145)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____5160 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,'Auu____5160) FStar_Pervasives_Native.tuple2
        Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____5190  ->
           match uu____5190 with
           | (y,uu____5196) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____5207 'Auu____5208 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv,'Auu____5207) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Syntax_Syntax.term,'Auu____5208)
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
                   let uu____5317 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____5317
                   then FStar_Pervasives_Native.None
                   else
                     (let uu____5325 =
                        let uu____5328 = FStar_Syntax_Syntax.mk_binder a  in
                        uu____5328 :: seen  in
                      aux uu____5325 args2)
               | uu____5329 -> FStar_Pervasives_Native.None)
           in
        aux [] args
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
    FStar_Pervasives_Native.tuple3[@@deriving show]
let flex_t_to_string :
  'Auu____5342 .
    ('Auu____5342,FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.args)
      FStar_Pervasives_Native.tuple3 -> Prims.string
  =
  fun uu____5353  ->
    match uu____5353 with
    | (uu____5360,c,args) ->
        let uu____5363 = print_ctx_uvar c  in
        let uu____5364 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____5363 uu____5364
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5370 =
      let uu____5371 = FStar_Syntax_Subst.compress t  in
      uu____5371.FStar_Syntax_Syntax.n  in
    match uu____5370 with
    | FStar_Syntax_Syntax.Tm_uvar uu____5374 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____5375;
           FStar_Syntax_Syntax.pos = uu____5376;
           FStar_Syntax_Syntax.vars = uu____5377;_},uu____5378)
        -> true
    | uu____5399 -> false
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> flex_t) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uvar uv -> (t, uv, [])
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uv;
           FStar_Syntax_Syntax.pos = uu____5417;
           FStar_Syntax_Syntax.vars = uu____5418;_},args)
        -> (t, uv, args)
    | uu____5440 -> failwith "Not a flex-uvar"
  
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | HeadMatch 
  | FullMatch [@@deriving show]
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____5468 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____5505 -> false
  
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____5511 -> false
  
let string_of_option :
  'Auu____5518 .
    ('Auu____5518 -> Prims.string) ->
      'Auu____5518 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___107_5533  ->
      match uu___107_5533 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____5539 = f x  in Prims.strcat "Some " uu____5539
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___108_5544  ->
    match uu___108_5544 with
    | MisMatch (d1,d2) ->
        let uu____5555 =
          let uu____5556 =
            string_of_option FStar_Syntax_Print.delta_depth_to_string d1  in
          let uu____5557 =
            let uu____5558 =
              let uu____5559 =
                string_of_option FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.strcat uu____5559 ")"  in
            Prims.strcat ") (" uu____5558  in
          Prims.strcat uu____5556 uu____5557  in
        Prims.strcat "MisMatch (" uu____5555
    | HeadMatch  -> "HeadMatch"
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___109_5564  ->
    match uu___109_5564 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____5579 -> HeadMatch
  
let (and_match : match_result -> (unit -> match_result) -> match_result) =
  fun m1  ->
    fun m2  ->
      match m1 with
      | MisMatch (i,j) -> MisMatch (i, j)
      | HeadMatch  ->
          let uu____5609 = m2 ()  in
          (match uu____5609 with
           | MisMatch (i,j) -> MisMatch (i, j)
           | uu____5624 -> HeadMatch)
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
          else FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____5637 ->
          let uu____5638 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____5638 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____5649 -> fv.FStar_Syntax_Syntax.fv_delta)
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
      | FStar_Syntax_Syntax.Tm_meta uu____5672 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____5681 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5709 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____5709
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____5710 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____5711 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____5712 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____5713 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____5726 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5750) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5756,uu____5757) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____5799) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____5820;
             FStar_Syntax_Syntax.index = uu____5821;
             FStar_Syntax_Syntax.sort = t2;_},uu____5823)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____5830 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____5831 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____5832 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____5845 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____5852 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____5870 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____5870
  
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
            let uu____5897 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____5897
            then FullMatch
            else
              (let uu____5899 =
                 let uu____5908 =
                   let uu____5911 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____5911  in
                 let uu____5912 =
                   let uu____5915 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____5915  in
                 (uu____5908, uu____5912)  in
               MisMatch uu____5899)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____5921),FStar_Syntax_Syntax.Tm_uinst (g,uu____5923)) ->
            let uu____5932 = head_matches env f g  in
            FStar_All.pipe_right uu____5932 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____5935 = FStar_Const.eq_const c d  in
            if uu____5935
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar uv,FStar_Syntax_Syntax.Tm_uvar uv') ->
            let uu____5943 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____5943
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____5950),FStar_Syntax_Syntax.Tm_refine (y,uu____5952)) ->
            let uu____5961 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5961 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____5963),uu____5964) ->
            let uu____5969 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____5969 head_match
        | (uu____5970,FStar_Syntax_Syntax.Tm_refine (x,uu____5972)) ->
            let uu____5977 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____5977 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____5978,FStar_Syntax_Syntax.Tm_type
           uu____5979) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____5980,FStar_Syntax_Syntax.Tm_arrow uu____5981) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____6007),FStar_Syntax_Syntax.Tm_app (head',uu____6009))
            ->
            let uu____6050 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____6050 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____6052),uu____6053) ->
            let uu____6074 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____6074 head_match
        | (uu____6075,FStar_Syntax_Syntax.Tm_app (head1,uu____6077)) ->
            let uu____6098 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____6098 head_match
        | uu____6099 ->
            let uu____6104 =
              let uu____6113 = delta_depth_of_term env t11  in
              let uu____6116 = delta_depth_of_term env t21  in
              (uu____6113, uu____6116)  in
            MisMatch uu____6104
  
let head_matches_delta :
  'Auu____6133 .
    FStar_TypeChecker_Env.env ->
      'Auu____6133 ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
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
            let uu____6172 = FStar_Syntax_Util.head_and_args t  in
            match uu____6172 with
            | (head1,uu____6190) ->
                let uu____6211 =
                  let uu____6212 = FStar_Syntax_Util.un_uinst head1  in
                  uu____6212.FStar_Syntax_Syntax.n  in
                (match uu____6211 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     let uu____6218 =
                       let uu____6219 =
                         FStar_TypeChecker_Env.lookup_definition
                           [FStar_TypeChecker_Env.Eager_unfolding_only] env
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          in
                       FStar_All.pipe_right uu____6219 FStar_Option.isSome
                        in
                     if uu____6218
                     then
                       let uu____6238 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Eager_unfolding] env t
                          in
                       FStar_All.pipe_right uu____6238
                         (fun _0_22  -> FStar_Pervasives_Native.Some _0_22)
                     else FStar_Pervasives_Native.None
                 | uu____6242 -> FStar_Pervasives_Native.None)
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
            match r with
            | MisMatch
                (FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ),uu____6363)
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6381 =
                     let uu____6390 = maybe_inline t11  in
                     let uu____6393 = maybe_inline t21  in
                     (uu____6390, uu____6393)  in
                   match uu____6381 with
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
                (uu____6430,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Delta_equational ))
                ->
                if Prims.op_Negation retry
                then fail1 r
                else
                  (let uu____6448 =
                     let uu____6457 = maybe_inline t11  in
                     let uu____6460 = maybe_inline t21  in
                     (uu____6457, uu____6460)  in
                   match uu____6448 with
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
                when d1 = d2 ->
                let uu____6503 = FStar_TypeChecker_Common.decr_delta_depth d1
                   in
                (match uu____6503 with
                 | FStar_Pervasives_Native.None  -> fail1 r
                 | FStar_Pervasives_Native.Some d ->
                     let t12 =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d;
                         FStar_TypeChecker_Normalize.Weak;
                         FStar_TypeChecker_Normalize.HNF] env wl t11
                        in
                     let t22 =
                       normalize_refinement
                         [FStar_TypeChecker_Normalize.UnfoldUntil d;
                         FStar_TypeChecker_Normalize.Weak;
                         FStar_TypeChecker_Normalize.HNF] env wl t21
                        in
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch
                (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some
                 d2)
                ->
                let d1_greater_than_d2 =
                  FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
                let uu____6526 =
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
                (match uu____6526 with
                 | (t12,t22) ->
                     aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
            | MisMatch uu____6550 -> fail1 r
            | uu____6559 -> success n_delta r t11 t21  in
          let r = aux true (Prims.parse_int "0") t1 t2  in
          (let uu____6572 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____6572
           then
             let uu____6573 = FStar_Syntax_Print.term_to_string t1  in
             let uu____6574 = FStar_Syntax_Print.term_to_string t2  in
             let uu____6575 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____6573
               uu____6574 uu____6575
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____6593 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____6593 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___110_6606  ->
    match uu___110_6606 with
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
      let uu___135_6643 = p  in
      let uu____6646 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____6647 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___135_6643.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____6646;
        FStar_TypeChecker_Common.relation =
          (uu___135_6643.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____6647;
        FStar_TypeChecker_Common.element =
          (uu___135_6643.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___135_6643.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___135_6643.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___135_6643.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___135_6643.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___135_6643.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____6661 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____6661
            (fun _0_23  -> FStar_TypeChecker_Common.TProb _0_23)
      | FStar_TypeChecker_Common.CProb uu____6666 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2)
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____6688 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____6688 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____6696 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____6696 with
           | (lh,lhs_args) ->
               let uu____6737 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____6737 with
                | (rh,rhs_args) ->
                    let uu____6778 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____6791,FStar_Syntax_Syntax.Tm_uvar uu____6792)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____6845 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____6868,uu____6869)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____6872,FStar_Syntax_Syntax.Tm_uvar uu____6873)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____6876,FStar_Syntax_Syntax.Tm_type uu____6877)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___136_6881 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___136_6881.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___136_6881.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___136_6881.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___136_6881.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___136_6881.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___136_6881.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___136_6881.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___136_6881.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___136_6881.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____6884,FStar_Syntax_Syntax.Tm_uvar uu____6885)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___136_6889 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___136_6889.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___136_6889.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___136_6889.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___136_6889.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___136_6889.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___136_6889.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___136_6889.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___136_6889.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___136_6889.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____6892,FStar_Syntax_Syntax.Tm_uvar uu____6893)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____6896,uu____6897)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____6900,FStar_Syntax_Syntax.Tm_uvar uu____6901)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____6904,uu____6905) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____6778 with
                     | (rank,tp1) ->
                         let uu____6918 =
                           FStar_All.pipe_right
                             (let uu___137_6922 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___137_6922.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___137_6922.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___137_6922.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___137_6922.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___137_6922.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___137_6922.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___137_6922.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___137_6922.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___137_6922.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_24  ->
                                FStar_TypeChecker_Common.TProb _0_24)
                            in
                         (rank, uu____6918))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____6928 =
            FStar_All.pipe_right
              (let uu___138_6932 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___138_6932.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___138_6932.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___138_6932.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___138_6932.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___138_6932.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___138_6932.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___138_6932.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___138_6932.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___138_6932.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _0_25  -> FStar_TypeChecker_Common.CProb _0_25)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____6928)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob,FStar_TypeChecker_Common.prob Prims.list,
      FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.tuple3
      FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____6993 probs =
      match uu____6993 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____7074 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____7095 = rank wl.tcenv hd1  in
               (match uu____7095 with
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
                      (let uu____7154 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____7158 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____7158)
                          in
                       if uu____7154
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
          let uu____7230 = destruct_flex_t t  in
          match uu____7230 with
          | (uu____7231,u,uu____7233) ->
              FStar_All.pipe_right u.FStar_Syntax_Syntax.ctx_uvar_binders
                (FStar_Util.for_some
                   (fun uu____7247  ->
                      match uu____7247 with
                      | (y,uu____7253) ->
                          FStar_All.pipe_right bs
                            (FStar_Util.for_some
                               (fun uu____7267  ->
                                  match uu____7267 with
                                  | (x,uu____7273) ->
                                      FStar_Syntax_Syntax.bv_eq x y))))
           in
        let uu____7274 = rank tcenv p  in
        match uu____7274 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____7281 -> true
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
    match projectee with | UDeferred _0 -> true | uu____7308 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____7322 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____7336 -> false
  
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
                        let uu____7388 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____7388 with
                        | (k,uu____7394) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____7404 -> false)))
            | uu____7405 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____7457 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____7463 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____7463 = (Prims.parse_int "0")))
                           in
                        if uu____7457 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____7479 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____7485 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____7485 = (Prims.parse_int "0")))
                      in
                   Prims.op_Negation uu____7479)
               in
            let uu____7486 = filter1 u12  in
            let uu____7489 = filter1 u22  in (uu____7486, uu____7489)  in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                let uu____7518 = filter_out_common_univs us1 us2  in
                (match uu____7518 with
                 | (us11,us21) ->
                     if (FStar_List.length us11) = (FStar_List.length us21)
                     then
                       let rec aux wl1 us12 us22 =
                         match (us12, us22) with
                         | (u13::us13,u23::us23) ->
                             let uu____7577 =
                               really_solve_universe_eq pid_orig wl1 u13 u23
                                in
                             (match uu____7577 with
                              | USolved wl2 -> aux wl2 us13 us23
                              | failed -> failed)
                         | uu____7580 -> USolved wl1  in
                       aux wl us11 us21
                     else
                       (let uu____7590 =
                          let uu____7591 =
                            FStar_Syntax_Print.univ_to_string u12  in
                          let uu____7592 =
                            FStar_Syntax_Print.univ_to_string u22  in
                          FStar_Util.format2
                            "Unable to unify universes: %s and %s" uu____7591
                            uu____7592
                           in
                        UFailed uu____7590))
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____7616 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____7616 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____7642 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____7642 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____7645 ->
                let uu____7650 =
                  let uu____7651 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____7652 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____7651
                    uu____7652 msg
                   in
                UFailed uu____7650
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____7653,uu____7654) ->
              let uu____7655 =
                let uu____7656 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____7657 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____7656 uu____7657
                 in
              failwith uu____7655
          | (FStar_Syntax_Syntax.U_unknown ,uu____7658) ->
              let uu____7659 =
                let uu____7660 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____7661 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____7660 uu____7661
                 in
              failwith uu____7659
          | (uu____7662,FStar_Syntax_Syntax.U_bvar uu____7663) ->
              let uu____7664 =
                let uu____7665 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____7666 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____7665 uu____7666
                 in
              failwith uu____7664
          | (uu____7667,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____7668 =
                let uu____7669 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____7670 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____7669 uu____7670
                 in
              failwith uu____7668
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____7694 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____7694
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____7708 = occurs_univ v1 u3  in
              if uu____7708
              then
                let uu____7709 =
                  let uu____7710 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____7711 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____7710 uu____7711
                   in
                try_umax_components u11 u21 uu____7709
              else
                (let uu____7713 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____7713)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____7725 = occurs_univ v1 u3  in
              if uu____7725
              then
                let uu____7726 =
                  let uu____7727 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____7728 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____7727 uu____7728
                   in
                try_umax_components u11 u21 uu____7726
              else
                (let uu____7730 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____7730)
          | (FStar_Syntax_Syntax.U_max uu____7731,uu____7732) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____7738 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____7738
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____7740,FStar_Syntax_Syntax.U_max uu____7741) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____7747 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____7747
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____7749,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____7750,FStar_Syntax_Syntax.U_name
             uu____7751) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____7752) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____7753) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____7754,FStar_Syntax_Syntax.U_succ
             uu____7755) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____7756,FStar_Syntax_Syntax.U_zero
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
      let uu____7856 = bc1  in
      match uu____7856 with
      | (bs1,mk_cod1) ->
          let uu____7900 = bc2  in
          (match uu____7900 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____8011 = aux xs ys  in
                     (match uu____8011 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____8094 =
                       let uu____8101 = mk_cod1 xs  in ([], uu____8101)  in
                     let uu____8104 =
                       let uu____8111 = mk_cod2 ys  in ([], uu____8111)  in
                     (uu____8094, uu____8104)
                  in
               aux bs1 bs2)
  
let is_flex_pat :
  'Auu____8134 'Auu____8135 'Auu____8136 .
    ('Auu____8134,'Auu____8135,'Auu____8136 Prims.list)
      FStar_Pervasives_Native.tuple3 -> Prims.bool
  =
  fun uu___111_8149  ->
    match uu___111_8149 with
    | (uu____8158,uu____8159,[]) -> true
    | uu____8162 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____8193 = f  in
      match uu____8193 with
      | (uu____8200,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____8201;
                      FStar_Syntax_Syntax.ctx_uvar_gamma = uu____8202;
                      FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                      FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                      FStar_Syntax_Syntax.ctx_uvar_reason = uu____8205;
                      FStar_Syntax_Syntax.ctx_uvar_should_check = uu____8206;
                      FStar_Syntax_Syntax.ctx_uvar_range = uu____8207;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____8259  ->
                 match uu____8259 with
                 | (y,uu____8265) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____8371 =
                  let uu____8380 =
                    let uu____8383 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____8383  in
                  ((FStar_List.rev pat_binders), uu____8380)  in
                FStar_Pervasives_Native.Some uu____8371
            | (uu____8398,[]) ->
                let uu____8421 =
                  let uu____8430 =
                    let uu____8433 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____8433  in
                  ((FStar_List.rev pat_binders), uu____8430)  in
                FStar_Pervasives_Native.Some uu____8421
            | ((formal,uu____8449)::formals1,(a,uu____8452)::args2) ->
                let uu____8486 =
                  let uu____8487 = FStar_Syntax_Subst.compress a  in
                  uu____8487.FStar_Syntax_Syntax.n  in
                (match uu____8486 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____8501 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____8501
                     then
                       let uu____8512 =
                         let uu____8515 =
                           FStar_Syntax_Syntax.mk_binder formal  in
                         uu____8515 :: pat_binders  in
                       aux uu____8512 formals1 t_res args2
                     else
                       (let x1 =
                          let uu___139_8518 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___139_8518.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___139_8518.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____8522 =
                            let uu____8523 =
                              let uu____8530 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____8530)  in
                            FStar_Syntax_Syntax.NT uu____8523  in
                          [uu____8522]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        let uu____8537 =
                          let uu____8540 =
                            FStar_Syntax_Syntax.mk_binder
                              (let uu___140_8543 = x1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___140_8543.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___140_8543.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort =
                                   (formal.FStar_Syntax_Syntax.sort)
                               })
                             in
                          uu____8540 :: pat_binders  in
                        aux uu____8537 formals2 t_res1 args2)
                 | uu____8544 ->
                     let uu____8545 =
                       let uu____8548 = FStar_Syntax_Syntax.mk_binder formal
                          in
                       uu____8548 :: pat_binders  in
                     aux uu____8545 formals1 t_res args2)
            | ([],args2) ->
                let uu____8572 =
                  let uu____8585 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____8585  in
                (match uu____8572 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____8636 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____8663 ->
               let uu____8664 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____8664 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____8936 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____8936
       then
         let uu____8937 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____8937
       else ());
      (let uu____8939 = next_prob probs  in
       match uu____8939 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___141_8966 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___141_8966.wl_deferred);
               ctr = (uu___141_8966.ctr);
               defer_ok = (uu___141_8966.defer_ok);
               smt_ok = (uu___141_8966.smt_ok);
               tcenv = (uu___141_8966.tcenv);
               wl_implicits = (uu___141_8966.wl_implicits)
             }  in
           (match hd1 with
            | FStar_TypeChecker_Common.CProb cp ->
                solve_c env (maybe_invert cp) probs1
            | FStar_TypeChecker_Common.TProb tp ->
                let uu____8973 =
                  FStar_Util.physical_equality
                    tp.FStar_TypeChecker_Common.lhs
                    tp.FStar_TypeChecker_Common.rhs
                   in
                if uu____8973
                then
                  let uu____8974 =
                    solve_prob hd1 FStar_Pervasives_Native.None [] probs1  in
                  solve env uu____8974
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
                          (let uu___142_8979 = tp  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___142_8979.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs =
                               (uu___142_8979.FStar_TypeChecker_Common.lhs);
                             FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.EQ;
                             FStar_TypeChecker_Common.rhs =
                               (uu___142_8979.FStar_TypeChecker_Common.rhs);
                             FStar_TypeChecker_Common.element =
                               (uu___142_8979.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___142_8979.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.logical_guard_uvar =
                               (uu___142_8979.FStar_TypeChecker_Common.logical_guard_uvar);
                             FStar_TypeChecker_Common.reason =
                               (uu___142_8979.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___142_8979.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___142_8979.FStar_TypeChecker_Common.rank)
                           }) probs1
                      else
                        solve_rigid_flex_or_flex_rigid_subtyping rank1 env tp
                          probs1)
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____9001 ->
                let uu____9010 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____9069  ->
                          match uu____9069 with
                          | (c,uu____9077,uu____9078) -> c < probs.ctr))
                   in
                (match uu____9010 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____9119 =
                            let uu____9124 =
                              FStar_List.map
                                (fun uu____9139  ->
                                   match uu____9139 with
                                   | (uu____9150,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____9124, (probs.wl_implicits))  in
                          Success uu____9119
                      | uu____9153 ->
                          let uu____9162 =
                            let uu___143_9163 = probs  in
                            let uu____9164 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____9183  ->
                                      match uu____9183 with
                                      | (uu____9190,uu____9191,y) -> y))
                               in
                            {
                              attempting = uu____9164;
                              wl_deferred = rest;
                              ctr = (uu___143_9163.ctr);
                              defer_ok = (uu___143_9163.defer_ok);
                              smt_ok = (uu___143_9163.smt_ok);
                              tcenv = (uu___143_9163.tcenv);
                              wl_implicits = (uu___143_9163.wl_implicits)
                            }  in
                          solve env uu____9162))))

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
            let uu____9198 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____9198 with
            | USolved wl1 ->
                let uu____9200 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____9200
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
                  let uu____9252 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____9252 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____9255 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____9267;
                  FStar_Syntax_Syntax.vars = uu____9268;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____9271;
                  FStar_Syntax_Syntax.vars = uu____9272;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____9284,uu____9285) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____9292,FStar_Syntax_Syntax.Tm_uinst uu____9293) ->
                failwith "Impossible: expect head symbols to match"
            | uu____9300 -> USolved wl

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
            ((let uu____9310 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____9310
              then
                let uu____9311 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____9311 msg
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
              let uu____9396 =
                new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                  FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                  "join/meet refinements"
                 in
              match uu____9396 with
              | (p,wl3) -> ((FStar_TypeChecker_Common.TProb p), wl3)  in
            let pairwise t1 t2 wl2 =
              (let uu____9448 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                   (FStar_Options.Other "RelCheck")
                  in
               if uu____9448
               then
                 let uu____9449 = FStar_Syntax_Print.term_to_string t1  in
                 let uu____9450 = FStar_Syntax_Print.term_to_string t2  in
                 FStar_Util.print2 "pairwise: %s and %s" uu____9449
                   uu____9450
               else ());
              (let uu____9452 = head_matches_delta env1 () t1 t2  in
               match uu____9452 with
               | (mr,ts1) ->
                   (match mr with
                    | MisMatch uu____9497 ->
                        let uu____9506 = eq_prob t1 t2 wl2  in
                        (match uu____9506 with | (p,wl3) -> (t1, [p], wl3))
                    | FullMatch  ->
                        (match ts1 with
                         | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             (t11, [], wl2))
                    | HeadMatch  ->
                        let uu____9553 =
                          match ts1 with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____9568 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____9569 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____9568, uu____9569)
                          | FStar_Pervasives_Native.None  ->
                              let uu____9574 = FStar_Syntax_Subst.compress t1
                                 in
                              let uu____9575 = FStar_Syntax_Subst.compress t2
                                 in
                              (uu____9574, uu____9575)
                           in
                        (match uu____9553 with
                         | (t11,t21) ->
                             let try_eq t12 t22 wl3 =
                               let uu____9606 =
                                 FStar_Syntax_Util.head_and_args t12  in
                               match uu____9606 with
                               | (t1_hd,t1_args) ->
                                   let uu____9645 =
                                     FStar_Syntax_Util.head_and_args t22  in
                                   (match uu____9645 with
                                    | (t2_hd,t2_args) ->
                                        if
                                          (FStar_List.length t1_args) <>
                                            (FStar_List.length t2_args)
                                        then FStar_Pervasives_Native.None
                                        else
                                          (let uu____9699 =
                                             let uu____9706 =
                                               let uu____9715 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t1_hd
                                                  in
                                               uu____9715 :: t1_args  in
                                             let uu____9728 =
                                               let uu____9735 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   t2_hd
                                                  in
                                               uu____9735 :: t2_args  in
                                             FStar_List.fold_left2
                                               (fun uu____9776  ->
                                                  fun uu____9777  ->
                                                    fun uu____9778  ->
                                                      match (uu____9776,
                                                              uu____9777,
                                                              uu____9778)
                                                      with
                                                      | ((probs,wl4),
                                                         (a1,uu____9820),
                                                         (a2,uu____9822)) ->
                                                          let uu____9847 =
                                                            eq_prob a1 a2 wl4
                                                             in
                                                          (match uu____9847
                                                           with
                                                           | (p,wl5) ->
                                                               ((p :: probs),
                                                                 wl5)))
                                               ([], wl3) uu____9706
                                               uu____9728
                                              in
                                           match uu____9699 with
                                           | (probs,wl4) ->
                                               let wl' =
                                                 let uu___144_9873 = wl4  in
                                                 {
                                                   attempting = probs;
                                                   wl_deferred = [];
                                                   ctr = (uu___144_9873.ctr);
                                                   defer_ok = false;
                                                   smt_ok = false;
                                                   tcenv =
                                                     (uu___144_9873.tcenv);
                                                   wl_implicits = []
                                                 }  in
                                               let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____9891 =
                                                 solve env1 wl'  in
                                               (match uu____9891 with
                                                | Success (uu____9894,imps)
                                                    ->
                                                    (FStar_Syntax_Unionfind.commit
                                                       tx;
                                                     FStar_Pervasives_Native.Some
                                                       ((let uu___145_9898 =
                                                           wl4  in
                                                         {
                                                           attempting =
                                                             (uu___145_9898.attempting);
                                                           wl_deferred =
                                                             (uu___145_9898.wl_deferred);
                                                           ctr =
                                                             (uu___145_9898.ctr);
                                                           defer_ok =
                                                             (uu___145_9898.defer_ok);
                                                           smt_ok =
                                                             (uu___145_9898.smt_ok);
                                                           tcenv =
                                                             (uu___145_9898.tcenv);
                                                           wl_implicits =
                                                             (FStar_List.append
                                                                wl4.wl_implicits
                                                                imps)
                                                         })))
                                                | Failed uu____9909 ->
                                                    (FStar_Syntax_Unionfind.rollback
                                                       tx;
                                                     FStar_Pervasives_Native.None))))
                                in
                             let combine t12 t22 wl3 =
                               let uu____9941 =
                                 base_and_refinement_maybe_delta false env1
                                   t12
                                  in
                               match uu____9941 with
                               | (t1_base,p1_opt) ->
                                   let uu____9982 =
                                     base_and_refinement_maybe_delta false
                                       env1 t22
                                      in
                                   (match uu____9982 with
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
                                              let uu____10113 =
                                                op phi11 phi21  in
                                              FStar_Syntax_Util.refine x1
                                                uu____10113
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
                                              let uu____10143 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              FStar_Syntax_Util.refine x1
                                                uu____10143
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
                                              let uu____10173 =
                                                op FStar_Syntax_Util.t_true
                                                  phi1
                                                 in
                                              FStar_Syntax_Util.refine x1
                                                uu____10173
                                          | uu____10176 -> t_base  in
                                        let uu____10193 =
                                          try_eq t1_base t2_base wl3  in
                                        (match uu____10193 with
                                         | FStar_Pervasives_Native.Some wl4
                                             ->
                                             let uu____10207 =
                                               combine_refinements t1_base
                                                 p1_opt p2_opt
                                                in
                                             (uu____10207, [], wl4)
                                         | FStar_Pervasives_Native.None  ->
                                             let uu____10214 =
                                               base_and_refinement_maybe_delta
                                                 true env1 t12
                                                in
                                             (match uu____10214 with
                                              | (t1_base1,p1_opt1) ->
                                                  let uu____10255 =
                                                    base_and_refinement_maybe_delta
                                                      true env1 t22
                                                     in
                                                  (match uu____10255 with
                                                   | (t2_base1,p2_opt1) ->
                                                       let uu____10296 =
                                                         eq_prob t1_base1
                                                           t2_base1 wl3
                                                          in
                                                       (match uu____10296
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
                             let uu____10320 = combine t11 t21 wl2  in
                             (match uu____10320 with
                              | (t12,ps,wl3) ->
                                  ((let uu____10353 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env1)
                                        (FStar_Options.Other "RelCheck")
                                       in
                                    if uu____10353
                                    then
                                      let uu____10354 =
                                        FStar_Syntax_Print.term_to_string t12
                                         in
                                      FStar_Util.print1
                                        "pairwise fallback2 succeeded: %s"
                                        uu____10354
                                    else ());
                                   (t12, ps, wl3))))))
               in
            let rec aux uu____10393 ts1 =
              match uu____10393 with
              | (out,probs,wl2) ->
                  (match ts1 with
                   | [] -> (out, probs, wl2)
                   | t::ts2 ->
                       let uu____10456 = pairwise out t wl2  in
                       (match uu____10456 with
                        | (out1,probs',wl3) ->
                            aux (out1, (FStar_List.append probs probs'), wl3)
                              ts2))
               in
            let uu____10492 =
              let uu____10503 = FStar_List.hd ts  in (uu____10503, [], wl1)
               in
            let uu____10512 = FStar_List.tl ts  in
            aux uu____10492 uu____10512  in
          let uu____10519 =
            if flip
            then
              ((tp.FStar_TypeChecker_Common.lhs),
                (tp.FStar_TypeChecker_Common.rhs))
            else
              ((tp.FStar_TypeChecker_Common.rhs),
                (tp.FStar_TypeChecker_Common.lhs))
             in
          match uu____10519 with
          | (this_flex,this_rigid) ->
              let uu____10531 =
                let uu____10532 = FStar_Syntax_Subst.compress this_rigid  in
                uu____10532.FStar_Syntax_Syntax.n  in
              (match uu____10531 with
               | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                   let uu____10553 =
                     FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                   if uu____10553
                   then
                     let flex = destruct_flex_t this_flex  in
                     let uu____10555 = quasi_pattern env flex  in
                     (match uu____10555 with
                      | FStar_Pervasives_Native.None  ->
                          giveup env
                            "flex-arrow subtyping, not a quasi pattern"
                            (FStar_TypeChecker_Common.TProb tp)
                      | FStar_Pervasives_Native.Some (flex_bs,flex_t) ->
                          ((let uu____10573 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "RelCheck")
                               in
                            if uu____10573
                            then
                              let uu____10574 =
                                FStar_Util.string_of_int
                                  tp.FStar_TypeChecker_Common.pid
                                 in
                              FStar_Util.print1
                                "Trying to solve by imitating arrow:%s\n"
                                uu____10574
                            else ());
                           imitate_arrow (FStar_TypeChecker_Common.TProb tp)
                             env wl flex flex_bs flex_t
                             tp.FStar_TypeChecker_Common.relation this_rigid))
                   else
                     solve env
                       (attempt
                          [FStar_TypeChecker_Common.TProb
                             ((let uu___146_10579 = tp  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___146_10579.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs =
                                   (uu___146_10579.FStar_TypeChecker_Common.lhs);
                                 FStar_TypeChecker_Common.relation =
                                   FStar_TypeChecker_Common.EQ;
                                 FStar_TypeChecker_Common.rhs =
                                   (uu___146_10579.FStar_TypeChecker_Common.rhs);
                                 FStar_TypeChecker_Common.element =
                                   (uu___146_10579.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___146_10579.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___146_10579.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___146_10579.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___146_10579.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___146_10579.FStar_TypeChecker_Common.rank)
                               }))] wl)
               | uu____10580 ->
                   ((let uu____10582 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelCheck")
                        in
                     if uu____10582
                     then
                       let uu____10583 =
                         FStar_Util.string_of_int
                           tp.FStar_TypeChecker_Common.pid
                          in
                       FStar_Util.print1
                         "Trying to solve by meeting refinements:%s\n"
                         uu____10583
                     else ());
                    (let uu____10585 =
                       FStar_Syntax_Util.head_and_args this_flex  in
                     match uu____10585 with
                     | (u,_args) ->
                         let uu____10622 =
                           let uu____10623 = FStar_Syntax_Subst.compress u
                              in
                           uu____10623.FStar_Syntax_Syntax.n  in
                         (match uu____10622 with
                          | FStar_Syntax_Syntax.Tm_uvar ctx_uvar ->
                              let equiv1 t =
                                let uu____10633 =
                                  FStar_Syntax_Util.head_and_args t  in
                                match uu____10633 with
                                | (u',uu____10649) ->
                                    let uu____10670 =
                                      let uu____10671 = whnf env u'  in
                                      uu____10671.FStar_Syntax_Syntax.n  in
                                    (match uu____10670 with
                                     | FStar_Syntax_Syntax.Tm_uvar ctx_uvar'
                                         ->
                                         FStar_Syntax_Unionfind.equiv
                                           ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                           ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                     | uu____10675 -> false)
                                 in
                              let uu____10676 =
                                FStar_All.pipe_right wl.attempting
                                  (FStar_List.partition
                                     (fun uu___112_10699  ->
                                        match uu___112_10699 with
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
                                             | uu____10708 -> false)
                                        | uu____10711 -> false))
                                 in
                              (match uu____10676 with
                               | (bounds_probs,rest) ->
                                   let bounds_typs =
                                     let uu____10725 = whnf env this_rigid
                                        in
                                     let uu____10726 =
                                       FStar_List.collect
                                         (fun uu___113_10732  ->
                                            match uu___113_10732 with
                                            | FStar_TypeChecker_Common.TProb
                                                p ->
                                                let uu____10738 =
                                                  if flip
                                                  then
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                  else
                                                    whnf env
                                                      (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                   in
                                                [uu____10738]
                                            | uu____10740 -> []) bounds_probs
                                        in
                                     uu____10725 :: uu____10726  in
                                   let uu____10741 =
                                     meet_or_join
                                       (if flip
                                        then FStar_Syntax_Util.mk_conj
                                        else FStar_Syntax_Util.mk_disj)
                                       bounds_typs env wl
                                      in
                                   (match uu____10741 with
                                    | (bound,sub_probs,wl1) ->
                                        let uu____10772 =
                                          let uu____10779 =
                                            destruct_flex_t this_flex  in
                                          match uu____10779 with
                                          | (uu____10786,flex_u,uu____10788)
                                              ->
                                              let bound1 =
                                                let uu____10790 =
                                                  let uu____10791 =
                                                    FStar_Syntax_Subst.compress
                                                      bound
                                                     in
                                                  uu____10791.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____10790 with
                                                | FStar_Syntax_Syntax.Tm_refine
                                                    (x,phi) when
                                                    (tp.FStar_TypeChecker_Common.relation
                                                       =
                                                       FStar_TypeChecker_Common.SUB)
                                                      &&
                                                      (let uu____10801 =
                                                         occurs flex_u
                                                           x.FStar_Syntax_Syntax.sort
                                                          in
                                                       FStar_Pervasives_Native.snd
                                                         uu____10801)
                                                    ->
                                                    x.FStar_Syntax_Syntax.sort
                                                | uu____10810 -> bound  in
                                              new_problem wl1 env bound1
                                                FStar_TypeChecker_Common.EQ
                                                this_flex
                                                FStar_Pervasives_Native.None
                                                tp.FStar_TypeChecker_Common.loc
                                                (if flip
                                                 then "joining refinements"
                                                 else "meeting refinements")
                                           in
                                        (match uu____10772 with
                                         | (eq_prob,wl2) ->
                                             ((let uu____10819 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other
                                                      "RelCheck")
                                                  in
                                               if uu____10819
                                               then
                                                 let wl' =
                                                   let uu___147_10821 = wl2
                                                      in
                                                   {
                                                     attempting =
                                                       ((FStar_TypeChecker_Common.TProb
                                                           eq_prob) ::
                                                       sub_probs);
                                                     wl_deferred =
                                                       (uu___147_10821.wl_deferred);
                                                     ctr =
                                                       (uu___147_10821.ctr);
                                                     defer_ok =
                                                       (uu___147_10821.defer_ok);
                                                     smt_ok =
                                                       (uu___147_10821.smt_ok);
                                                     tcenv =
                                                       (uu___147_10821.tcenv);
                                                     wl_implicits =
                                                       (uu___147_10821.wl_implicits)
                                                   }  in
                                                 let uu____10822 =
                                                   wl_to_string wl'  in
                                                 FStar_Util.print1
                                                   "After meet/join refinements: %s\n"
                                                   uu____10822
                                               else ());
                                              (let tx =
                                                 FStar_Syntax_Unionfind.new_transaction
                                                   ()
                                                  in
                                               let uu____10825 =
                                                 solve_t env eq_prob
                                                   (let uu___148_10827 = wl2
                                                       in
                                                    {
                                                      attempting = sub_probs;
                                                      wl_deferred =
                                                        (uu___148_10827.wl_deferred);
                                                      ctr =
                                                        (uu___148_10827.ctr);
                                                      defer_ok =
                                                        (uu___148_10827.defer_ok);
                                                      smt_ok =
                                                        (uu___148_10827.smt_ok);
                                                      tcenv =
                                                        (uu___148_10827.tcenv);
                                                      wl_implicits =
                                                        (uu___148_10827.wl_implicits)
                                                    })
                                                  in
                                               match uu____10825 with
                                               | Success uu____10828 ->
                                                   let wl3 =
                                                     let uu___149_10834 = wl2
                                                        in
                                                     {
                                                       attempting = rest;
                                                       wl_deferred =
                                                         (uu___149_10834.wl_deferred);
                                                       ctr =
                                                         (uu___149_10834.ctr);
                                                       defer_ok =
                                                         (uu___149_10834.defer_ok);
                                                       smt_ok =
                                                         (uu___149_10834.smt_ok);
                                                       tcenv =
                                                         (uu___149_10834.tcenv);
                                                       wl_implicits =
                                                         (uu___149_10834.wl_implicits)
                                                     }  in
                                                   let wl4 =
                                                     solve_prob' false
                                                       (FStar_TypeChecker_Common.TProb
                                                          tp)
                                                       FStar_Pervasives_Native.None
                                                       [] wl3
                                                      in
                                                   let uu____10838 =
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
                                                    giveup env
                                                      (Prims.strcat
                                                         "failed to solve sub-problems: "
                                                         msg) p))))))
                          | uu____10849 when flip ->
                              let uu____10850 =
                                let uu____10851 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format1
                                  "Impossible: Not a flex-rigid: %s"
                                  uu____10851
                                 in
                              failwith uu____10850
                          | uu____10852 ->
                              let uu____10853 =
                                let uu____10854 =
                                  prob_to_string env
                                    (FStar_TypeChecker_Common.TProb tp)
                                   in
                                FStar_Util.format1
                                  "Impossible: Not a rigid-flex: %s"
                                  uu____10854
                                 in
                              failwith uu____10853))))

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
                      (fun uu____10882  ->
                         match uu____10882 with
                         | (x,i) ->
                             let uu____10893 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____10893, i)) bs_lhs
                     in
                  let uu____10894 = lhs  in
                  match uu____10894 with
                  | (uu____10895,u_lhs,uu____10897) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____11010 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____11020 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____11020, univ)
                             in
                          match uu____11010 with
                          | (k,univ) ->
                              let uu____11033 =
                                let uu____11040 =
                                  let uu____11043 =
                                    FStar_Syntax_Syntax.mk_Total k  in
                                  FStar_Syntax_Util.arrow
                                    (FStar_List.append bs_lhs bs) uu____11043
                                   in
                                copy_uvar u_lhs uu____11040 wl2  in
                              (match uu____11033 with
                               | (uu____11056,u,wl3) ->
                                   let uu____11059 =
                                     let uu____11062 =
                                       FStar_Syntax_Syntax.mk_Tm_app u
                                         (FStar_List.append bs_lhs_args
                                            bs_terms)
                                         FStar_Pervasives_Native.None
                                         c.FStar_Syntax_Syntax.pos
                                        in
                                     f uu____11062
                                       (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____11059, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____11098 =
                              let uu____11111 =
                                let uu____11120 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____11120 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____11166  ->
                                   fun uu____11167  ->
                                     match (uu____11166, uu____11167) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____11258 =
                                           let uu____11265 =
                                             let uu____11268 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____11268
                                              in
                                           copy_uvar u_lhs uu____11265 wl2
                                            in
                                         (match uu____11258 with
                                          | (uu____11291,t_a,wl3) ->
                                              let uu____11294 =
                                                let uu____11301 =
                                                  let uu____11304 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      t_a
                                                     in
                                                  FStar_Syntax_Util.arrow bs
                                                    uu____11304
                                                   in
                                                copy_uvar u_lhs uu____11301
                                                  wl3
                                                 in
                                              (match uu____11294 with
                                               | (uu____11319,a',wl4) ->
                                                   let a'1 =
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       a' bs_terms
                                                       FStar_Pervasives_Native.None
                                                       a.FStar_Syntax_Syntax.pos
                                                      in
                                                   (((a'1, i) :: out_args),
                                                     wl4)))) uu____11111
                                ([], wl1)
                               in
                            (match uu____11098 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___150_11380 = ct  in
                                   let uu____11381 =
                                     let uu____11384 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____11384
                                      in
                                   let uu____11399 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___150_11380.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___150_11380.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____11381;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____11399;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___150_11380.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___151_11417 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___151_11417.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___151_11417.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____11420 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____11420 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____11474 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____11474 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____11491 =
                                          let uu____11496 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____11496)  in
                                        TERM uu____11491  in
                                      let uu____11497 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____11497 with
                                       | (sub_prob,wl3) ->
                                           let uu____11508 =
                                             let uu____11509 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____11509
                                              in
                                           solve env uu____11508))
                             | (x,imp)::formals2 ->
                                 let uu____11523 =
                                   let uu____11530 =
                                     let uu____11533 =
                                       let uu____11536 =
                                         let uu____11537 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____11537
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.mk_Total
                                         uu____11536
                                        in
                                     FStar_Syntax_Util.arrow
                                       (FStar_List.append bs_lhs bs)
                                       uu____11533
                                      in
                                   copy_uvar u_lhs uu____11530 wl1  in
                                 (match uu____11523 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let t_y =
                                        FStar_Syntax_Syntax.mk_Tm_app u_x
                                          (FStar_List.append bs_lhs_args
                                             bs_terms)
                                          FStar_Pervasives_Native.None
                                          (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                         in
                                      let y =
                                        let uu____11561 =
                                          let uu____11564 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____11564
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____11561 t_y
                                         in
                                      let uu____11565 =
                                        let uu____11568 =
                                          let uu____11571 =
                                            let uu____11572 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____11572, imp)  in
                                          [uu____11571]  in
                                        FStar_List.append bs_terms
                                          uu____11568
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____11565 formals2 wl2)
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
              (let uu____11614 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____11614
               then
                 let uu____11615 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____11616 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____11615 (rel_to_string (p_rel orig)) uu____11616
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____11721 = rhs wl1 scope env1 subst1  in
                     (match uu____11721 with
                      | (rhs_prob,wl2) ->
                          ((let uu____11741 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____11741
                            then
                              let uu____11742 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____11742
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                     let hd11 =
                       let uu___152_11796 = hd1  in
                       let uu____11797 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___152_11796.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___152_11796.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____11797
                       }  in
                     let hd21 =
                       let uu___153_11801 = hd2  in
                       let uu____11802 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___153_11801.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___153_11801.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____11802
                       }  in
                     let uu____11805 =
                       let uu____11810 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____11810
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____11805 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____11829 =
                              FStar_Syntax_Subst.shift_subst
                                (Prims.parse_int "1") subst1
                               in
                            (FStar_Syntax_Syntax.DB
                               ((Prims.parse_int "0"), hd12))
                              :: uu____11829
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____11833 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____11833 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____11888 =
                                   close_forall env2 [(hd12, imp)] phi  in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____11888
                                  in
                               ((let uu____11900 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____11900
                                 then
                                   let uu____11901 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____11902 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____11901
                                     uu____11902
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____11929 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____11958 = aux wl [] env [] bs1 bs2  in
               match uu____11958 with
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
        (let uu____12009 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____12009 wl)

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
              let uu____12023 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____12023 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____12053 = lhs1  in
              match uu____12053 with
              | (uu____12056,ctx_u,uu____12058) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____12064 ->
                        let uu____12065 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____12065 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____12112 = quasi_pattern env1 lhs1  in
              match uu____12112 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____12142) ->
                  let uu____12147 = lhs1  in
                  (match uu____12147 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____12161 = occurs_check ctx_u rhs1  in
                       (match uu____12161 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____12203 =
                                let uu____12210 =
                                  let uu____12211 = FStar_Option.get msg  in
                                  Prims.strcat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____12211
                                   in
                                FStar_Util.Inl uu____12210  in
                              (uu____12203, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____12231 =
                                 let uu____12232 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____12232  in
                               if uu____12231
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____12252 =
                                    let uu____12259 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____12259  in
                                  let uu____12264 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____12252, uu____12264)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let bs_lhs_args =
                FStar_List.map
                  (fun uu____12326  ->
                     match uu____12326 with
                     | (x,i) ->
                         let uu____12337 = FStar_Syntax_Syntax.bv_to_name x
                            in
                         (uu____12337, i)) bs_lhs
                 in
              let uu____12338 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____12338 with
              | (rhs_hd,args) ->
                  let uu____12375 = FStar_Util.prefix args  in
                  (match uu____12375 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____12433 = lhs1  in
                       (match uu____12433 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____12437 =
                              let uu____12448 =
                                let uu____12455 =
                                  let uu____12458 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____12458
                                   in
                                copy_uvar u_lhs uu____12455 wl1  in
                              match uu____12448 with
                              | (uu____12479,t_last_arg,wl2) ->
                                  let uu____12482 =
                                    let uu____12489 =
                                      let uu____12492 =
                                        let uu____12499 =
                                          let uu____12506 =
                                            FStar_Syntax_Syntax.null_binder
                                              t_last_arg
                                             in
                                          [uu____12506]  in
                                        FStar_List.append bs_lhs uu____12499
                                         in
                                      let uu____12523 =
                                        FStar_Syntax_Syntax.mk_Total
                                          t_res_lhs
                                         in
                                      FStar_Syntax_Util.arrow uu____12492
                                        uu____12523
                                       in
                                    copy_uvar u_lhs uu____12489 wl2  in
                                  (match uu____12482 with
                                   | (uu____12536,u_lhs',wl3) ->
                                       let lhs' =
                                         FStar_Syntax_Syntax.mk_Tm_app u_lhs'
                                           bs_lhs_args
                                           FStar_Pervasives_Native.None
                                           t_lhs.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____12542 =
                                         let uu____12549 =
                                           let uu____12552 =
                                             FStar_Syntax_Syntax.mk_Total
                                               t_last_arg
                                              in
                                           FStar_Syntax_Util.arrow bs_lhs
                                             uu____12552
                                            in
                                         copy_uvar u_lhs uu____12549 wl3  in
                                       (match uu____12542 with
                                        | (uu____12565,u_lhs'_last_arg,wl4)
                                            ->
                                            let lhs'_last_arg =
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                u_lhs'_last_arg bs_lhs_args
                                                FStar_Pervasives_Native.None
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____12437 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____12589 =
                                     let uu____12590 =
                                       let uu____12595 =
                                         let uu____12596 =
                                           let uu____12599 =
                                             let uu____12604 =
                                               let uu____12605 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____12605]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____12604
                                              in
                                           uu____12599
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____12596
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____12595)  in
                                     TERM uu____12590  in
                                   [uu____12589]  in
                                 let uu____12626 =
                                   let uu____12633 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____12633 with
                                   | (p1,wl3) ->
                                       let uu____12650 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____12650 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____12626 with
                                  | (sub_probs,wl3) ->
                                      let uu____12677 =
                                        let uu____12678 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____12678  in
                                      solve env1 uu____12677))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____12711 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____12711 with
                | (uu____12726,args) ->
                    (match args with | [] -> false | uu____12754 -> true)
                 in
              let is_arrow rhs2 =
                let uu____12769 =
                  let uu____12770 = FStar_Syntax_Subst.compress rhs2  in
                  uu____12770.FStar_Syntax_Syntax.n  in
                match uu____12769 with
                | FStar_Syntax_Syntax.Tm_arrow uu____12773 -> true
                | uu____12786 -> false  in
              let uu____12787 = quasi_pattern env1 lhs1  in
              match uu____12787 with
              | FStar_Pervasives_Native.None  ->
                  let uu____12798 =
                    let uu____12799 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heursitic cannot solve %s; lhs not a quasi-pattern"
                      uu____12799
                     in
                  giveup_or_defer env1 orig1 wl1 uu____12798
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____12806 = is_app rhs1  in
                  if uu____12806
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____12808 = is_arrow rhs1  in
                     if uu____12808
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____12810 =
                          let uu____12811 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heursitic cannot solve %s; rhs not an app or arrow"
                            uu____12811
                           in
                        giveup_or_defer env1 orig1 wl1 uu____12810))
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
                let uu____12814 = lhs  in
                (match uu____12814 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____12818 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____12818 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____12833 =
                              let uu____12836 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____12836
                               in
                            FStar_All.pipe_right uu____12833
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____12851 = occurs_check ctx_uv rhs1  in
                          (match uu____12851 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____12873 =
                                   let uu____12874 = FStar_Option.get msg  in
                                   Prims.strcat "occurs-check failed: "
                                     uu____12874
                                    in
                                 giveup_or_defer env orig wl uu____12873
                               else
                                 (let uu____12876 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____12876
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____12881 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____12881
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____12883 =
                                         let uu____12884 =
                                           names_to_string1 fvs2  in
                                         let uu____12885 =
                                           names_to_string1 fvs1  in
                                         let uu____12886 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____12884 uu____12885
                                           uu____12886
                                          in
                                       giveup_or_defer env orig wl
                                         uu____12883)
                                    else first_order orig env wl lhs rhs1))
                      | uu____12892 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____12896 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____12896 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____12919 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____12919
                             | (FStar_Util.Inl msg,uu____12921) ->
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
                  (let uu____12950 =
                     let uu____12967 = quasi_pattern env lhs  in
                     let uu____12974 = quasi_pattern env rhs  in
                     (uu____12967, uu____12974)  in
                   match uu____12950 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____13017 = lhs  in
                       (match uu____13017 with
                        | ({ FStar_Syntax_Syntax.n = uu____13018;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____13020;_},u_lhs,uu____13022)
                            ->
                            let uu____13025 = rhs  in
                            (match uu____13025 with
                             | (uu____13026,u_rhs,uu____13028) ->
                                 let uu____13029 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____13029
                                 then
                                   let uu____13030 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____13030
                                 else
                                   (let uu____13032 =
                                      mk_t_problem wl [] orig t_res_lhs
                                        FStar_TypeChecker_Common.EQ t_res_rhs
                                        FStar_Pervasives_Native.None
                                        "flex-flex typing"
                                       in
                                    match uu____13032 with
                                    | (sub_prob,wl1) ->
                                        let uu____13043 =
                                          maximal_prefix
                                            u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                            u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                           in
                                        (match uu____13043 with
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
                                             let uu____13071 =
                                               let uu____13078 =
                                                 let uu____13081 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t_res_lhs
                                                    in
                                                 FStar_Syntax_Util.arrow zs
                                                   uu____13081
                                                  in
                                               new_uvar
                                                 (Prims.strcat
                                                    "flex-flex quasi: lhs="
                                                    (Prims.strcat
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                       (Prims.strcat ", rhs="
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason)))
                                                 wl1 range gamma_w ctx_w
                                                 uu____13078
                                                 (u_lhs.FStar_Syntax_Syntax.ctx_uvar_should_check
                                                    ||
                                                    u_rhs.FStar_Syntax_Syntax.ctx_uvar_should_check)
                                                in
                                             (match uu____13071 with
                                              | (uu____13084,w,wl2) ->
                                                  let w_app =
                                                    let uu____13090 =
                                                      let uu____13095 =
                                                        FStar_List.map
                                                          (fun uu____13104 
                                                             ->
                                                             match uu____13104
                                                             with
                                                             | (z,uu____13110)
                                                                 ->
                                                                 let uu____13111
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    z
                                                                    in
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   uu____13111)
                                                          zs
                                                         in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        w uu____13095
                                                       in
                                                    uu____13090
                                                      FStar_Pervasives_Native.None
                                                      w.FStar_Syntax_Syntax.pos
                                                     in
                                                  ((let uu____13115 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "RelCheck")
                                                       in
                                                    if uu____13115
                                                    then
                                                      let uu____13116 =
                                                        flex_t_to_string lhs
                                                         in
                                                      let uu____13117 =
                                                        flex_t_to_string rhs
                                                         in
                                                      let uu____13118 =
                                                        let uu____13119 =
                                                          destruct_flex_t w
                                                           in
                                                        flex_t_to_string
                                                          uu____13119
                                                         in
                                                      FStar_Util.print3
                                                        "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s"
                                                        uu____13116
                                                        uu____13117
                                                        uu____13118
                                                    else ());
                                                   (let sol =
                                                      let s1 =
                                                        let uu____13131 =
                                                          let uu____13136 =
                                                            FStar_Syntax_Util.abs
                                                              binders_lhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_lhs,
                                                            uu____13136)
                                                           in
                                                        TERM uu____13131  in
                                                      let uu____13137 =
                                                        FStar_Syntax_Unionfind.equiv
                                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                         in
                                                      if uu____13137
                                                      then [s1]
                                                      else
                                                        (let s2 =
                                                           let uu____13142 =
                                                             let uu____13147
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
                                                               uu____13147)
                                                              in
                                                           TERM uu____13142
                                                            in
                                                         [s1; s2])
                                                       in
                                                    let uu____13148 =
                                                      let uu____13149 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          sol wl2
                                                         in
                                                      attempt [sub_prob]
                                                        uu____13149
                                                       in
                                                    solve env uu____13148)))))))
                   | uu____13150 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
           let uu____13218 = head_matches_delta env1 wl1 t1 t2  in
           match uu____13218 with
           | (m,o) ->
               (match (m, o) with
                | (MisMatch uu____13249,uu____13250) ->
                    let rec may_relate head3 =
                      let uu____13277 =
                        let uu____13278 = FStar_Syntax_Subst.compress head3
                           in
                        uu____13278.FStar_Syntax_Syntax.n  in
                      match uu____13277 with
                      | FStar_Syntax_Syntax.Tm_name uu____13281 -> true
                      | FStar_Syntax_Syntax.Tm_match uu____13282 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____13305;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_equational ;
                            FStar_Syntax_Syntax.fv_qual = uu____13306;_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____13309;
                            FStar_Syntax_Syntax.fv_delta =
                              FStar_Syntax_Syntax.Delta_abstract uu____13310;
                            FStar_Syntax_Syntax.fv_qual = uu____13311;_}
                          ->
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                      | FStar_Syntax_Syntax.Tm_ascribed
                          (t,uu____13315,uu____13316) -> may_relate t
                      | FStar_Syntax_Syntax.Tm_uinst (t,uu____13358) ->
                          may_relate t
                      | FStar_Syntax_Syntax.Tm_meta (t,uu____13364) ->
                          may_relate t
                      | uu____13369 -> false  in
                    let uu____13370 =
                      ((may_relate head1) || (may_relate head2)) &&
                        wl1.smt_ok
                       in
                    if uu____13370
                    then
                      let uu____13371 =
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
                                 let uu____13403 =
                                   let uu____13404 =
                                     FStar_Syntax_Syntax.bv_to_name x  in
                                   FStar_Syntax_Util.mk_has_type t11
                                     uu____13404 t21
                                    in
                                 FStar_Syntax_Util.mk_forall u_x x
                                   uu____13403
                              in
                           if
                             problem.FStar_TypeChecker_Common.relation =
                               FStar_TypeChecker_Common.SUB
                           then
                             let uu____13409 = has_type_guard t1 t2  in
                             (uu____13409, wl1)
                           else
                             (let uu____13415 = has_type_guard t2 t1  in
                              (uu____13415, wl1)))
                         in
                      (match uu____13371 with
                       | (guard,wl2) ->
                           let uu____13422 =
                             solve_prob orig
                               (FStar_Pervasives_Native.Some guard) [] wl2
                              in
                           solve env1 uu____13422)
                    else
                      (let uu____13424 =
                         let uu____13425 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____13426 =
                           FStar_Syntax_Print.term_to_string head2  in
                         FStar_Util.format2 "head mismatch (%s vs %s)"
                           uu____13425 uu____13426
                          in
                       giveup env1 uu____13424 orig)
                | (uu____13427,FStar_Pervasives_Native.Some (t11,t21)) ->
                    solve_t env1
                      (let uu___154_13441 = problem  in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___154_13441.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = t11;
                         FStar_TypeChecker_Common.relation =
                           (uu___154_13441.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = t21;
                         FStar_TypeChecker_Common.element =
                           (uu___154_13441.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___154_13441.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___154_13441.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___154_13441.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___154_13441.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___154_13441.FStar_TypeChecker_Common.rank)
                       }) wl1
                | (uu____13442,FStar_Pervasives_Native.None ) ->
                    ((let uu____13454 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13454
                      then
                        let uu____13455 =
                          FStar_Syntax_Print.term_to_string t1  in
                        let uu____13456 = FStar_Syntax_Print.tag_of_term t1
                           in
                        let uu____13457 =
                          FStar_Syntax_Print.term_to_string t2  in
                        let uu____13458 = FStar_Syntax_Print.tag_of_term t2
                           in
                        FStar_Util.print4
                          "Head matches: %s (%s) and %s (%s)\n" uu____13455
                          uu____13456 uu____13457 uu____13458
                      else ());
                     (let uu____13460 = FStar_Syntax_Util.head_and_args t1
                         in
                      match uu____13460 with
                      | (head11,args1) ->
                          let uu____13497 =
                            FStar_Syntax_Util.head_and_args t2  in
                          (match uu____13497 with
                           | (head21,args2) ->
                               let nargs = FStar_List.length args1  in
                               if nargs <> (FStar_List.length args2)
                               then
                                 let uu____13551 =
                                   let uu____13552 =
                                     FStar_Syntax_Print.term_to_string head11
                                      in
                                   let uu____13553 = args_to_string args1  in
                                   let uu____13554 =
                                     FStar_Syntax_Print.term_to_string head21
                                      in
                                   let uu____13555 = args_to_string args2  in
                                   FStar_Util.format4
                                     "unequal number of arguments: %s[%s] and %s[%s]"
                                     uu____13552 uu____13553 uu____13554
                                     uu____13555
                                    in
                                 giveup env1 uu____13551 orig
                               else
                                 (let uu____13557 =
                                    (nargs = (Prims.parse_int "0")) ||
                                      (let uu____13564 =
                                         FStar_Syntax_Util.eq_args args1
                                           args2
                                          in
                                       uu____13564 = FStar_Syntax_Util.Equal)
                                     in
                                  if uu____13557
                                  then
                                    let uu____13565 =
                                      solve_maybe_uinsts env1 orig head11
                                        head21 wl1
                                       in
                                    match uu____13565 with
                                    | USolved wl2 ->
                                        let uu____13567 =
                                          solve_prob orig
                                            FStar_Pervasives_Native.None []
                                            wl2
                                           in
                                        solve env1 uu____13567
                                    | UFailed msg -> giveup env1 msg orig
                                    | UDeferred wl2 ->
                                        solve env1
                                          (defer "universe constraints" orig
                                             wl2)
                                  else
                                    (let uu____13571 =
                                       base_and_refinement env1 t1  in
                                     match uu____13571 with
                                     | (base1,refinement1) ->
                                         let uu____13596 =
                                           base_and_refinement env1 t2  in
                                         (match uu____13596 with
                                          | (base2,refinement2) ->
                                              (match (refinement1,
                                                       refinement2)
                                               with
                                               | (FStar_Pervasives_Native.None
                                                  ,FStar_Pervasives_Native.None
                                                  ) ->
                                                   let uu____13653 =
                                                     solve_maybe_uinsts env1
                                                       orig head11 head21 wl1
                                                      in
                                                   (match uu____13653 with
                                                    | UFailed msg ->
                                                        giveup env1 msg orig
                                                    | UDeferred wl2 ->
                                                        solve env1
                                                          (defer
                                                             "universe constraints"
                                                             orig wl2)
                                                    | USolved wl2 ->
                                                        let uu____13657 =
                                                          FStar_List.fold_right2
                                                            (fun uu____13690 
                                                               ->
                                                               fun
                                                                 uu____13691 
                                                                 ->
                                                                 fun
                                                                   uu____13692
                                                                    ->
                                                                   match 
                                                                    (uu____13690,
                                                                    uu____13691,
                                                                    uu____13692)
                                                                   with
                                                                   | 
                                                                   ((a,uu____13728),
                                                                    (a',uu____13730),
                                                                    (subprobs,wl3))
                                                                    ->
                                                                    let uu____13751
                                                                    =
                                                                    mk_t_problem
                                                                    wl3 []
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a'
                                                                    FStar_Pervasives_Native.None
                                                                    "index"
                                                                     in
                                                                    (match uu____13751
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
                                                        (match uu____13657
                                                         with
                                                         | (subprobs,wl3) ->
                                                             let formula =
                                                               let uu____13781
                                                                 =
                                                                 FStar_List.map
                                                                   (fun p  ->
                                                                    p_guard p)
                                                                   subprobs
                                                                  in
                                                               FStar_Syntax_Util.mk_conj_l
                                                                 uu____13781
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
                                                                  wl4)))
                                               | uu____13789 ->
                                                   let lhs =
                                                     force_refinement
                                                       (base1, refinement1)
                                                      in
                                                   let rhs =
                                                     force_refinement
                                                       (base2, refinement2)
                                                      in
                                                   solve_t env1
                                                     (let uu___155_13829 =
                                                        problem  in
                                                      {
                                                        FStar_TypeChecker_Common.pid
                                                          =
                                                          (uu___155_13829.FStar_TypeChecker_Common.pid);
                                                        FStar_TypeChecker_Common.lhs
                                                          = lhs;
                                                        FStar_TypeChecker_Common.relation
                                                          =
                                                          (uu___155_13829.FStar_TypeChecker_Common.relation);
                                                        FStar_TypeChecker_Common.rhs
                                                          = rhs;
                                                        FStar_TypeChecker_Common.element
                                                          =
                                                          (uu___155_13829.FStar_TypeChecker_Common.element);
                                                        FStar_TypeChecker_Common.logical_guard
                                                          =
                                                          (uu___155_13829.FStar_TypeChecker_Common.logical_guard);
                                                        FStar_TypeChecker_Common.logical_guard_uvar
                                                          =
                                                          (uu___155_13829.FStar_TypeChecker_Common.logical_guard_uvar);
                                                        FStar_TypeChecker_Common.reason
                                                          =
                                                          (uu___155_13829.FStar_TypeChecker_Common.reason);
                                                        FStar_TypeChecker_Common.loc
                                                          =
                                                          (uu___155_13829.FStar_TypeChecker_Common.loc);
                                                        FStar_TypeChecker_Common.rank
                                                          =
                                                          (uu___155_13829.FStar_TypeChecker_Common.rank)
                                                      }) wl1))))))))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____13832 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____13832
          then
            let uu____13833 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____13833
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____13838 =
                FStar_TypeChecker_Env.debug env
                  (FStar_Options.Other "RelCheck")
                 in
              if uu____13838
              then
                let uu____13839 = FStar_Syntax_Print.tag_of_term t1  in
                let uu____13840 = FStar_Syntax_Print.tag_of_term t2  in
                let uu____13841 = prob_to_string env orig  in
                FStar_Util.print3 "Attempting (%s - %s)\n%s\n" uu____13839
                  uu____13840 uu____13841
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____13844,uu____13845) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____13870,FStar_Syntax_Syntax.Tm_delayed uu____13871) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____13896,uu____13897) ->
                  let uu____13924 =
                    let uu___156_13925 = problem  in
                    let uu____13926 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___156_13925.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____13926;
                      FStar_TypeChecker_Common.relation =
                        (uu___156_13925.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___156_13925.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___156_13925.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___156_13925.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___156_13925.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___156_13925.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___156_13925.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___156_13925.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____13924 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____13927,uu____13928) ->
                  let uu____13935 =
                    let uu___157_13936 = problem  in
                    let uu____13937 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___157_13936.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____13937;
                      FStar_TypeChecker_Common.relation =
                        (uu___157_13936.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___157_13936.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___157_13936.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___157_13936.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___157_13936.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___157_13936.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___157_13936.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___157_13936.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____13935 wl
              | (uu____13938,FStar_Syntax_Syntax.Tm_ascribed uu____13939) ->
                  let uu____13966 =
                    let uu___158_13967 = problem  in
                    let uu____13968 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___158_13967.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___158_13967.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___158_13967.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____13968;
                      FStar_TypeChecker_Common.element =
                        (uu___158_13967.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___158_13967.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___158_13967.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___158_13967.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___158_13967.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___158_13967.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____13966 wl
              | (uu____13969,FStar_Syntax_Syntax.Tm_meta uu____13970) ->
                  let uu____13977 =
                    let uu___159_13978 = problem  in
                    let uu____13979 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___159_13978.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___159_13978.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___159_13978.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____13979;
                      FStar_TypeChecker_Common.element =
                        (uu___159_13978.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___159_13978.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___159_13978.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___159_13978.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___159_13978.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___159_13978.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____13977 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____13981),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____13983)) ->
                  let uu____13992 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____13992
              | (FStar_Syntax_Syntax.Tm_bvar uu____13993,uu____13994) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____13995,FStar_Syntax_Syntax.Tm_bvar uu____13996) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___114_14055 =
                    match uu___114_14055 with
                    | [] -> c
                    | bs ->
                        let uu____14077 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____14077
                     in
                  let uu____14086 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____14086 with
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
                                    let uu____14209 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____14209
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
                  let mk_t t l uu___115_14284 =
                    match uu___115_14284 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____14318 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____14318 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____14437 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____14438 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____14437
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____14438 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____14439,uu____14440) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____14467 -> true
                    | uu____14484 -> false  in
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
                      (let uu____14525 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___160_14533 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___160_14533.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___160_14533.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___160_14533.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___160_14533.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___160_14533.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___160_14533.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___160_14533.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___160_14533.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___160_14533.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___160_14533.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___160_14533.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___160_14533.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___160_14533.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___160_14533.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___160_14533.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___160_14533.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___160_14533.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___160_14533.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___160_14533.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___160_14533.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___160_14533.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___160_14533.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___160_14533.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___160_14533.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___160_14533.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___160_14533.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___160_14533.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___160_14533.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___160_14533.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___160_14533.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___160_14533.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___160_14533.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___160_14533.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___160_14533.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___160_14533.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____14525 with
                       | (uu____14536,ty,uu____14538) ->
                           let uu____14539 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____14539)
                     in
                  let uu____14540 =
                    let uu____14553 = maybe_eta t1  in
                    let uu____14558 = maybe_eta t2  in
                    (uu____14553, uu____14558)  in
                  (match uu____14540 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___161_14582 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___161_14582.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___161_14582.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___161_14582.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___161_14582.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___161_14582.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___161_14582.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___161_14582.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___161_14582.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____14593 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____14593
                       then
                         let uu____14594 = destruct_flex_t not_abs  in
                         solve_t_flex_rigid_eq env orig wl uu____14594 t_abs
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___162_14603 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___162_14603.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___162_14603.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___162_14603.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___162_14603.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___162_14603.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___162_14603.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___162_14603.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___162_14603.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____14615 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____14615
                       then
                         let uu____14616 = destruct_flex_t not_abs  in
                         solve_t_flex_rigid_eq env orig wl uu____14616 t_abs
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___162_14625 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___162_14625.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___162_14625.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___162_14625.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___162_14625.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___162_14625.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___162_14625.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___162_14625.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___162_14625.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____14627 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____14640,FStar_Syntax_Syntax.Tm_abs uu____14641) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____14668 -> true
                    | uu____14685 -> false  in
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
                      (let uu____14726 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___160_14734 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___160_14734.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___160_14734.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___160_14734.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___160_14734.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___160_14734.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___160_14734.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___160_14734.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___160_14734.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___160_14734.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___160_14734.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___160_14734.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___160_14734.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___160_14734.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___160_14734.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___160_14734.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___160_14734.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___160_14734.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___160_14734.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___160_14734.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___160_14734.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___160_14734.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___160_14734.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___160_14734.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___160_14734.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___160_14734.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___160_14734.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___160_14734.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___160_14734.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___160_14734.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___160_14734.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___160_14734.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___160_14734.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___160_14734.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___160_14734.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___160_14734.FStar_TypeChecker_Env.dep_graph)
                            }) t
                          in
                       match uu____14726 with
                       | (uu____14737,ty,uu____14739) ->
                           let uu____14740 =
                             FStar_TypeChecker_Normalize.unfold_whnf env ty
                              in
                           FStar_TypeChecker_Normalize.eta_expand_with_type
                             env t uu____14740)
                     in
                  let uu____14741 =
                    let uu____14754 = maybe_eta t1  in
                    let uu____14759 = maybe_eta t2  in
                    (uu____14754, uu____14759)  in
                  (match uu____14741 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___161_14783 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___161_14783.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___161_14783.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___161_14783.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___161_14783.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___161_14783.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___161_14783.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___161_14783.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___161_14783.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____14794 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____14794
                       then
                         let uu____14795 = destruct_flex_t not_abs  in
                         solve_t_flex_rigid_eq env orig wl uu____14795 t_abs
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___162_14804 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___162_14804.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___162_14804.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___162_14804.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___162_14804.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___162_14804.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___162_14804.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___162_14804.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___162_14804.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____14816 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____14816
                       then
                         let uu____14817 = destruct_flex_t not_abs  in
                         solve_t_flex_rigid_eq env orig wl uu____14817 t_abs
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___162_14826 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___162_14826.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___162_14826.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___162_14826.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___162_14826.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___162_14826.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___162_14826.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___162_14826.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___162_14826.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____14828 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,ph1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let should_delta =
                    ((let uu____14856 = FStar_Syntax_Free.uvars t1  in
                      FStar_Util.set_is_empty uu____14856) &&
                       (let uu____14860 = FStar_Syntax_Free.uvars t2  in
                        FStar_Util.set_is_empty uu____14860))
                      &&
                      (let uu____14867 =
                         head_matches env x1.FStar_Syntax_Syntax.sort
                           x2.FStar_Syntax_Syntax.sort
                          in
                       match uu____14867 with
                       | MisMatch
                           (FStar_Pervasives_Native.Some
                            d1,FStar_Pervasives_Native.Some d2)
                           ->
                           let is_unfoldable uu___116_14879 =
                             match uu___116_14879 with
                             | FStar_Syntax_Syntax.Delta_constant  -> true
                             | FStar_Syntax_Syntax.Delta_defined_at_level
                                 uu____14880 -> true
                             | uu____14881 -> false  in
                           (is_unfoldable d1) && (is_unfoldable d2)
                       | uu____14882 -> false)
                     in
                  let uu____14883 = as_refinement should_delta env wl t1  in
                  (match uu____14883 with
                   | (x11,phi1) ->
                       let uu____14890 = as_refinement should_delta env wl t2
                          in
                       (match uu____14890 with
                        | (x21,phi21) ->
                            let uu____14897 =
                              mk_t_problem wl [] orig
                                x11.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.relation
                                x21.FStar_Syntax_Syntax.sort
                                problem.FStar_TypeChecker_Common.element
                                "refinement base type"
                               in
                            (match uu____14897 with
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
                                   let uu____14963 = imp phi12 phi23  in
                                   FStar_All.pipe_right uu____14963
                                     (guard_on_element wl1 problem x12)
                                    in
                                 let fallback uu____14975 =
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
                                   let uu____14986 =
                                     let uu____14991 =
                                       let uu____14998 =
                                         FStar_Syntax_Syntax.mk_binder x12
                                          in
                                       [uu____14998]  in
                                     mk_t_problem wl1 uu____14991 orig phi11
                                       FStar_TypeChecker_Common.EQ phi22
                                       FStar_Pervasives_Native.None
                                       "refinement formula"
                                      in
                                   (match uu____14986 with
                                    | (ref_prob,wl2) ->
                                        let uu____15013 =
                                          solve env1
                                            (let uu___163_15015 = wl2  in
                                             {
                                               attempting = [ref_prob];
                                               wl_deferred = [];
                                               ctr = (uu___163_15015.ctr);
                                               defer_ok = false;
                                               smt_ok =
                                                 (uu___163_15015.smt_ok);
                                               tcenv = (uu___163_15015.tcenv);
                                               wl_implicits =
                                                 (uu___163_15015.wl_implicits)
                                             })
                                           in
                                        (match uu____15013 with
                                         | Failed uu____15022 -> fallback ()
                                         | Success uu____15027 ->
                                             let guard =
                                               let uu____15035 =
                                                 FStar_All.pipe_right
                                                   (p_guard ref_prob)
                                                   (guard_on_element wl2
                                                      problem x12)
                                                  in
                                               FStar_Syntax_Util.mk_conj
                                                 (p_guard base_prob)
                                                 uu____15035
                                                in
                                             let wl3 =
                                               solve_prob orig
                                                 (FStar_Pervasives_Native.Some
                                                    guard) [] wl2
                                                in
                                             let wl4 =
                                               let uu___164_15044 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___164_15044.attempting);
                                                 wl_deferred =
                                                   (uu___164_15044.wl_deferred);
                                                 ctr =
                                                   (wl3.ctr +
                                                      (Prims.parse_int "1"));
                                                 defer_ok =
                                                   (uu___164_15044.defer_ok);
                                                 smt_ok =
                                                   (uu___164_15044.smt_ok);
                                                 tcenv =
                                                   (uu___164_15044.tcenv);
                                                 wl_implicits =
                                                   (uu___164_15044.wl_implicits)
                                               }  in
                                             solve env1
                                               (attempt [base_prob] wl4)))
                                 else fallback ())))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____15046,FStar_Syntax_Syntax.Tm_uvar uu____15047) ->
                  let uu____15048 = destruct_flex_t t1  in
                  let uu____15049 = destruct_flex_t t2  in
                  solve_t_flex_flex env orig wl uu____15048 uu____15049
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15050;
                    FStar_Syntax_Syntax.pos = uu____15051;
                    FStar_Syntax_Syntax.vars = uu____15052;_},uu____15053),FStar_Syntax_Syntax.Tm_uvar
                 uu____15054) ->
                  let uu____15075 = destruct_flex_t t1  in
                  let uu____15076 = destruct_flex_t t2  in
                  solve_t_flex_flex env orig wl uu____15075 uu____15076
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____15077,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15078;
                    FStar_Syntax_Syntax.pos = uu____15079;
                    FStar_Syntax_Syntax.vars = uu____15080;_},uu____15081))
                  ->
                  let uu____15102 = destruct_flex_t t1  in
                  let uu____15103 = destruct_flex_t t2  in
                  solve_t_flex_flex env orig wl uu____15102 uu____15103
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15104;
                    FStar_Syntax_Syntax.pos = uu____15105;
                    FStar_Syntax_Syntax.vars = uu____15106;_},uu____15107),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15108;
                    FStar_Syntax_Syntax.pos = uu____15109;
                    FStar_Syntax_Syntax.vars = uu____15110;_},uu____15111))
                  ->
                  let uu____15152 = destruct_flex_t t1  in
                  let uu____15153 = destruct_flex_t t2  in
                  solve_t_flex_flex env orig wl uu____15152 uu____15153
              | (FStar_Syntax_Syntax.Tm_uvar uu____15154,uu____15155) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____15156 = destruct_flex_t t1  in
                  solve_t_flex_rigid_eq env orig wl uu____15156 t2
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15157;
                    FStar_Syntax_Syntax.pos = uu____15158;
                    FStar_Syntax_Syntax.vars = uu____15159;_},uu____15160),uu____15161)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____15182 = destruct_flex_t t1  in
                  solve_t_flex_rigid_eq env orig wl uu____15182 t2
              | (uu____15183,FStar_Syntax_Syntax.Tm_uvar uu____15184) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____15185,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15186;
                    FStar_Syntax_Syntax.pos = uu____15187;
                    FStar_Syntax_Syntax.vars = uu____15188;_},uu____15189))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____15210,FStar_Syntax_Syntax.Tm_arrow uu____15211) ->
                  solve_t' env
                    (let uu___165_15225 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___165_15225.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___165_15225.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___165_15225.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___165_15225.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___165_15225.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___165_15225.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___165_15225.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___165_15225.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___165_15225.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15226;
                    FStar_Syntax_Syntax.pos = uu____15227;
                    FStar_Syntax_Syntax.vars = uu____15228;_},uu____15229),FStar_Syntax_Syntax.Tm_arrow
                 uu____15230) ->
                  solve_t' env
                    (let uu___165_15264 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___165_15264.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___165_15264.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___165_15264.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___165_15264.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___165_15264.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___165_15264.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___165_15264.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___165_15264.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___165_15264.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____15265,FStar_Syntax_Syntax.Tm_uvar uu____15266) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (uu____15267,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15268;
                    FStar_Syntax_Syntax.pos = uu____15269;
                    FStar_Syntax_Syntax.vars = uu____15270;_},uu____15271))
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_uvar uu____15292,uu____15293) ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____15294;
                    FStar_Syntax_Syntax.pos = uu____15295;
                    FStar_Syntax_Syntax.vars = uu____15296;_},uu____15297),uu____15298)
                  ->
                  solve env
                    (attempt [FStar_TypeChecker_Common.TProb problem] wl)
              | (FStar_Syntax_Syntax.Tm_refine uu____15319,uu____15320) ->
                  let t21 =
                    let uu____15328 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____15328  in
                  solve_t env
                    (let uu___166_15354 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___166_15354.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___166_15354.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___166_15354.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___166_15354.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___166_15354.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___166_15354.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___166_15354.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___166_15354.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___166_15354.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____15355,FStar_Syntax_Syntax.Tm_refine uu____15356) ->
                  let t11 =
                    let uu____15364 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____15364  in
                  solve_t env
                    (let uu___167_15390 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___167_15390.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___167_15390.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___167_15390.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___167_15390.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___167_15390.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___167_15390.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___167_15390.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___167_15390.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___167_15390.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (t11,brs1),FStar_Syntax_Syntax.Tm_match (t21,brs2)) ->
                  let uu____15467 =
                    mk_t_problem wl [] orig t11 FStar_TypeChecker_Common.EQ
                      t21 FStar_Pervasives_Native.None "match scrutinee"
                     in
                  (match uu____15467 with
                   | (sc_prob,wl1) ->
                       let rec solve_branches wl2 brs11 brs21 =
                         match (brs11, brs21) with
                         | (br1::rs1,br2::rs2) ->
                             let uu____15688 = br1  in
                             (match uu____15688 with
                              | (p1,w1,uu____15713) ->
                                  let uu____15730 = br2  in
                                  (match uu____15730 with
                                   | (p2,w2,uu____15749) ->
                                       let uu____15754 =
                                         let uu____15755 =
                                           FStar_Syntax_Syntax.eq_pat p1 p2
                                            in
                                         Prims.op_Negation uu____15755  in
                                       if uu____15754
                                       then FStar_Pervasives_Native.None
                                       else
                                         (let uu____15771 =
                                            FStar_Syntax_Subst.open_branch'
                                              br1
                                             in
                                          match uu____15771 with
                                          | ((p11,w11,e1),s) ->
                                              let uu____15804 = br2  in
                                              (match uu____15804 with
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
                                                     let uu____15839 =
                                                       FStar_Syntax_Syntax.pat_bvs
                                                         p11
                                                        in
                                                     FStar_All.pipe_left
                                                       (FStar_List.map
                                                          FStar_Syntax_Syntax.mk_binder)
                                                       uu____15839
                                                      in
                                                   let uu____15850 =
                                                     match (w11, w22) with
                                                     | (FStar_Pervasives_Native.Some
                                                        uu____15873,FStar_Pervasives_Native.None
                                                        ) ->
                                                         FStar_Pervasives_Native.None
                                                     | (FStar_Pervasives_Native.None
                                                        ,FStar_Pervasives_Native.Some
                                                        uu____15890) ->
                                                         FStar_Pervasives_Native.None
                                                     | (FStar_Pervasives_Native.None
                                                        ,FStar_Pervasives_Native.None
                                                        ) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([], wl2)
                                                     | (FStar_Pervasives_Native.Some
                                                        w12,FStar_Pervasives_Native.Some
                                                        w23) ->
                                                         let uu____15933 =
                                                           mk_t_problem wl2
                                                             scope orig w12
                                                             FStar_TypeChecker_Common.EQ
                                                             w23
                                                             FStar_Pervasives_Native.None
                                                             "when clause"
                                                            in
                                                         (match uu____15933
                                                          with
                                                          | (p,wl3) ->
                                                              FStar_Pervasives_Native.Some
                                                                ([p], wl3))
                                                      in
                                                   FStar_Util.bind_opt
                                                     uu____15850
                                                     (fun uu____15975  ->
                                                        match uu____15975
                                                        with
                                                        | (wprobs,wl3) ->
                                                            let uu____15996 =
                                                              mk_t_problem
                                                                wl3 scope
                                                                orig e1
                                                                FStar_TypeChecker_Common.EQ
                                                                e21
                                                                FStar_Pervasives_Native.None
                                                                "branch body"
                                                               in
                                                            (match uu____15996
                                                             with
                                                             | (prob,wl4) ->
                                                                 let uu____16011
                                                                   =
                                                                   solve_branches
                                                                    wl4 rs1
                                                                    rs2
                                                                    in
                                                                 FStar_Util.bind_opt
                                                                   uu____16011
                                                                   (fun
                                                                    uu____16035
                                                                     ->
                                                                    match uu____16035
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
                         | uu____16120 -> FStar_Pervasives_Native.None  in
                       let uu____16157 = solve_branches wl1 brs1 brs2  in
                       (match uu____16157 with
                        | FStar_Pervasives_Native.None  ->
                            giveup env "Tm_match branches don't match" orig
                        | FStar_Pervasives_Native.Some (sub_probs,wl2) ->
                            let sub_probs1 = sc_prob :: sub_probs  in
                            let wl3 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl2
                               in
                            solve env (attempt sub_probs1 wl3)))
              | (FStar_Syntax_Syntax.Tm_match uu____16188,uu____16189) ->
                  let head1 =
                    let uu____16213 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16213
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16253 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16253
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16293 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16293
                    then
                      let uu____16294 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16295 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16296 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16294 uu____16295 uu____16296
                    else ());
                   (let uu____16298 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16298
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16305 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16305
                       then
                         let uu____16306 =
                           let uu____16313 =
                             let uu____16314 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16314 = FStar_Syntax_Util.Equal  in
                           if uu____16313
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16324 = mk_eq2 wl orig t1 t2  in
                              match uu____16324 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16306 with
                         | (guard,wl1) ->
                             let uu____16345 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16345
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____16348,uu____16349) ->
                  let head1 =
                    let uu____16357 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16357
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16397 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16397
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16437 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16437
                    then
                      let uu____16438 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16439 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16440 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16438 uu____16439 uu____16440
                    else ());
                   (let uu____16442 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16442
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16449 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16449
                       then
                         let uu____16450 =
                           let uu____16457 =
                             let uu____16458 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16458 = FStar_Syntax_Util.Equal  in
                           if uu____16457
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16468 = mk_eq2 wl orig t1 t2  in
                              match uu____16468 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16450 with
                         | (guard,wl1) ->
                             let uu____16489 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16489
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____16492,uu____16493) ->
                  let head1 =
                    let uu____16495 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16495
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16535 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16535
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16575 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16575
                    then
                      let uu____16576 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16577 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16578 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16576 uu____16577 uu____16578
                    else ());
                   (let uu____16580 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16580
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16587 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16587
                       then
                         let uu____16588 =
                           let uu____16595 =
                             let uu____16596 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16596 = FStar_Syntax_Util.Equal  in
                           if uu____16595
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16606 = mk_eq2 wl orig t1 t2  in
                              match uu____16606 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16588 with
                         | (guard,wl1) ->
                             let uu____16627 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16627
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____16630,uu____16631) ->
                  let head1 =
                    let uu____16633 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16633
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16673 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16673
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16713 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16713
                    then
                      let uu____16714 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16715 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16716 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16714 uu____16715 uu____16716
                    else ());
                   (let uu____16718 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16718
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16725 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16725
                       then
                         let uu____16726 =
                           let uu____16733 =
                             let uu____16734 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16734 = FStar_Syntax_Util.Equal  in
                           if uu____16733
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16744 = mk_eq2 wl orig t1 t2  in
                              match uu____16744 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16726 with
                         | (guard,wl1) ->
                             let uu____16765 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16765
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____16768,uu____16769) ->
                  let head1 =
                    let uu____16771 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16771
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16811 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16811
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____16851 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____16851
                    then
                      let uu____16852 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____16853 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____16854 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____16852 uu____16853 uu____16854
                    else ());
                   (let uu____16856 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____16856
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____16863 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____16863
                       then
                         let uu____16864 =
                           let uu____16871 =
                             let uu____16872 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____16872 = FStar_Syntax_Util.Equal  in
                           if uu____16871
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____16882 = mk_eq2 wl orig t1 t2  in
                              match uu____16882 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____16864 with
                         | (guard,wl1) ->
                             let uu____16903 = solve_prob orig guard [] wl1
                                in
                             solve env uu____16903
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____16906,uu____16907) ->
                  let head1 =
                    let uu____16923 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____16923
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____16963 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____16963
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17003 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____17003
                    then
                      let uu____17004 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17005 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17006 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17004 uu____17005 uu____17006
                    else ());
                   (let uu____17008 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17008
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17015 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17015
                       then
                         let uu____17016 =
                           let uu____17023 =
                             let uu____17024 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17024 = FStar_Syntax_Util.Equal  in
                           if uu____17023
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17034 = mk_eq2 wl orig t1 t2  in
                              match uu____17034 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17016 with
                         | (guard,wl1) ->
                             let uu____17055 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17055
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____17058,FStar_Syntax_Syntax.Tm_match uu____17059) ->
                  let head1 =
                    let uu____17083 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17083
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17123 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17123
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17163 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____17163
                    then
                      let uu____17164 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17165 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17166 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17164 uu____17165 uu____17166
                    else ());
                   (let uu____17168 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17168
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17175 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17175
                       then
                         let uu____17176 =
                           let uu____17183 =
                             let uu____17184 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17184 = FStar_Syntax_Util.Equal  in
                           if uu____17183
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17194 = mk_eq2 wl orig t1 t2  in
                              match uu____17194 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17176 with
                         | (guard,wl1) ->
                             let uu____17215 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17215
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____17218,FStar_Syntax_Syntax.Tm_uinst uu____17219) ->
                  let head1 =
                    let uu____17227 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17227
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17267 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17267
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17307 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____17307
                    then
                      let uu____17308 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17309 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17310 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17308 uu____17309 uu____17310
                    else ());
                   (let uu____17312 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17312
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17319 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17319
                       then
                         let uu____17320 =
                           let uu____17327 =
                             let uu____17328 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17328 = FStar_Syntax_Util.Equal  in
                           if uu____17327
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17338 = mk_eq2 wl orig t1 t2  in
                              match uu____17338 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17320 with
                         | (guard,wl1) ->
                             let uu____17359 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17359
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____17362,FStar_Syntax_Syntax.Tm_name uu____17363) ->
                  let head1 =
                    let uu____17365 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17365
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17405 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17405
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17445 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____17445
                    then
                      let uu____17446 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17447 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17448 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17446 uu____17447 uu____17448
                    else ());
                   (let uu____17450 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17450
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17457 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17457
                       then
                         let uu____17458 =
                           let uu____17465 =
                             let uu____17466 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17466 = FStar_Syntax_Util.Equal  in
                           if uu____17465
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17476 = mk_eq2 wl orig t1 t2  in
                              match uu____17476 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17458 with
                         | (guard,wl1) ->
                             let uu____17497 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17497
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____17500,FStar_Syntax_Syntax.Tm_constant uu____17501) ->
                  let head1 =
                    let uu____17503 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17503
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17543 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17543
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17583 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____17583
                    then
                      let uu____17584 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17585 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17586 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17584 uu____17585 uu____17586
                    else ());
                   (let uu____17588 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17588
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17595 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17595
                       then
                         let uu____17596 =
                           let uu____17603 =
                             let uu____17604 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17604 = FStar_Syntax_Util.Equal  in
                           if uu____17603
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17614 = mk_eq2 wl orig t1 t2  in
                              match uu____17614 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17596 with
                         | (guard,wl1) ->
                             let uu____17635 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17635
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____17638,FStar_Syntax_Syntax.Tm_fvar uu____17639) ->
                  let head1 =
                    let uu____17641 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17641
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17681 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17681
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17721 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____17721
                    then
                      let uu____17722 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17723 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17724 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17722 uu____17723 uu____17724
                    else ());
                   (let uu____17726 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17726
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17733 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17733
                       then
                         let uu____17734 =
                           let uu____17741 =
                             let uu____17742 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17742 = FStar_Syntax_Util.Equal  in
                           if uu____17741
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17752 = mk_eq2 wl orig t1 t2  in
                              match uu____17752 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17734 with
                         | (guard,wl1) ->
                             let uu____17773 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17773
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (uu____17776,FStar_Syntax_Syntax.Tm_app uu____17777) ->
                  let head1 =
                    let uu____17793 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____17793
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____17833 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____17833
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____17873 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "RelCheck")
                       in
                    if uu____17873
                    then
                      let uu____17874 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____17875 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____17876 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____17874 uu____17875 uu____17876
                    else ());
                   (let uu____17878 =
                      (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                          (FStar_TypeChecker_Env.is_interpreted env head2))
                         && wl.smt_ok)
                        &&
                        (problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ)
                       in
                    if uu____17878
                    then
                      let uv1 = FStar_Syntax_Free.uvars t1  in
                      let uv2 = FStar_Syntax_Free.uvars t2  in
                      let uu____17885 =
                        (FStar_Util.set_is_empty uv1) &&
                          (FStar_Util.set_is_empty uv2)
                         in
                      (if uu____17885
                       then
                         let uu____17886 =
                           let uu____17893 =
                             let uu____17894 = FStar_Syntax_Util.eq_tm t1 t2
                                in
                             uu____17894 = FStar_Syntax_Util.Equal  in
                           if uu____17893
                           then (FStar_Pervasives_Native.None, wl)
                           else
                             (let uu____17904 = mk_eq2 wl orig t1 t2  in
                              match uu____17904 with
                              | (g,wl1) ->
                                  ((FStar_Pervasives_Native.Some g), wl1))
                            in
                         match uu____17886 with
                         | (guard,wl1) ->
                             let uu____17925 = solve_prob orig guard [] wl1
                                in
                             solve env uu____17925
                       else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                    else rigid_rigid_delta env orig wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____17928,FStar_Syntax_Syntax.Tm_let uu____17929) ->
                  let uu____17954 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____17954
                  then
                    let uu____17955 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____17955
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____17957,uu____17958) ->
                  let uu____17971 =
                    let uu____17976 =
                      let uu____17977 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____17978 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____17979 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____17980 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____17977 uu____17978 uu____17979 uu____17980
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____17976)
                     in
                  FStar_Errors.raise_error uu____17971
                    t1.FStar_Syntax_Syntax.pos
              | (uu____17981,FStar_Syntax_Syntax.Tm_let uu____17982) ->
                  let uu____17995 =
                    let uu____18000 =
                      let uu____18001 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____18002 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____18003 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____18004 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____18001 uu____18002 uu____18003 uu____18004
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____18000)
                     in
                  FStar_Errors.raise_error uu____17995
                    t1.FStar_Syntax_Syntax.pos
              | uu____18005 -> giveup env "head tag mismatch" orig))))

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
          (let uu____18064 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____18064
           then
             let uu____18065 =
               let uu____18066 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____18066  in
             let uu____18067 =
               let uu____18068 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____18068  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____18065 uu____18067
           else ());
          (let uu____18070 =
             let uu____18071 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____18071  in
           if uu____18070
           then
             let uu____18072 =
               let uu____18073 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____18074 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____18073 uu____18074
                in
             giveup env uu____18072 orig
           else
             (let uu____18076 =
                sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                  FStar_TypeChecker_Common.EQ
                  c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                 in
              match uu____18076 with
              | (ret_sub_prob,wl1) ->
                  let uu____18083 =
                    FStar_List.fold_right2
                      (fun uu____18116  ->
                         fun uu____18117  ->
                           fun uu____18118  ->
                             match (uu____18116, uu____18117, uu____18118)
                             with
                             | ((a1,uu____18154),(a2,uu____18156),(arg_sub_probs,wl2))
                                 ->
                                 let uu____18177 =
                                   sub_prob wl2 a1
                                     FStar_TypeChecker_Common.EQ a2
                                     "effect arg"
                                    in
                                 (match uu____18177 with
                                  | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                      c1_comp.FStar_Syntax_Syntax.effect_args
                      c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                     in
                  (match uu____18083 with
                   | (arg_sub_probs,wl2) ->
                       let sub_probs = ret_sub_prob :: arg_sub_probs  in
                       let guard =
                         let uu____18206 = FStar_List.map p_guard sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____18206  in
                       let wl3 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl2
                          in
                       solve env (attempt sub_probs wl3))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____18236 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____18239)::[] -> wp1
              | uu____18256 ->
                  let uu____18265 =
                    let uu____18266 =
                      let uu____18267 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____18267  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____18266
                     in
                  failwith uu____18265
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____18273 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____18273]
              | x -> x  in
            let uu____18275 =
              let uu____18284 =
                let uu____18291 =
                  let uu____18292 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____18292 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____18291  in
              [uu____18284]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____18275;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____18305 = lift_c1 ()  in solve_eq uu____18305 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___117_18311  ->
                       match uu___117_18311 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____18312 -> false))
                in
             let uu____18313 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____18347)::uu____18348,(wp2,uu____18350)::uu____18351)
                   -> (wp1, wp2)
               | uu____18408 ->
                   let uu____18429 =
                     let uu____18434 =
                       let uu____18435 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____18436 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____18435 uu____18436
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____18434)
                      in
                   FStar_Errors.raise_error uu____18429
                     env.FStar_TypeChecker_Env.range
                in
             match uu____18313 with
             | (wpc1,wpc2) ->
                 let uu____18455 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____18455
                 then
                   let uu____18458 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____18458 wl
                 else
                   (let uu____18460 =
                      let uu____18467 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____18467  in
                    match uu____18460 with
                    | (c2_decl,qualifiers) ->
                        let uu____18488 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____18488
                        then
                          let c1_repr =
                            let uu____18492 =
                              let uu____18493 =
                                let uu____18494 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____18494  in
                              let uu____18495 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____18493 uu____18495
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____18492
                             in
                          let c2_repr =
                            let uu____18497 =
                              let uu____18498 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____18499 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____18498 uu____18499
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.Weak;
                              FStar_TypeChecker_Normalize.HNF] env
                              uu____18497
                             in
                          let uu____18500 =
                            let uu____18505 =
                              let uu____18506 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____18507 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____18506 uu____18507
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____18505
                             in
                          (match uu____18500 with
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
                                 ((let uu____18521 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____18521
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____18524 =
                                     let uu____18531 =
                                       let uu____18532 =
                                         let uu____18547 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____18550 =
                                           let uu____18559 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____18566 =
                                             let uu____18575 =
                                               let uu____18582 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____18582
                                                in
                                             [uu____18575]  in
                                           uu____18559 :: uu____18566  in
                                         (uu____18547, uu____18550)  in
                                       FStar_Syntax_Syntax.Tm_app uu____18532
                                        in
                                     FStar_Syntax_Syntax.mk uu____18531  in
                                   uu____18524 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____18623 =
                                    let uu____18630 =
                                      let uu____18631 =
                                        let uu____18646 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____18649 =
                                          let uu____18658 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____18665 =
                                            let uu____18674 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____18681 =
                                              let uu____18690 =
                                                let uu____18697 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____18697
                                                 in
                                              [uu____18690]  in
                                            uu____18674 :: uu____18681  in
                                          uu____18658 :: uu____18665  in
                                        (uu____18646, uu____18649)  in
                                      FStar_Syntax_Syntax.Tm_app uu____18631
                                       in
                                    FStar_Syntax_Syntax.mk uu____18630  in
                                  uu____18623 FStar_Pervasives_Native.None r)
                              in
                           let uu____18741 =
                             sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                               problem.FStar_TypeChecker_Common.relation
                               c21.FStar_Syntax_Syntax.result_typ
                               "result type"
                              in
                           match uu____18741 with
                           | (base_prob,wl1) ->
                               let wl2 =
                                 let uu____18749 =
                                   let uu____18752 =
                                     FStar_Syntax_Util.mk_conj
                                       (p_guard base_prob) g
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_26  ->
                                        FStar_Pervasives_Native.Some _0_26)
                                     uu____18752
                                    in
                                 solve_prob orig uu____18749 [] wl1  in
                               solve env (attempt [base_prob] wl2))))
           in
        let uu____18755 = FStar_Util.physical_equality c1 c2  in
        if uu____18755
        then
          let uu____18756 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____18756
        else
          ((let uu____18759 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____18759
            then
              let uu____18760 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____18761 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____18760
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____18761
            else ());
           (let uu____18763 =
              let uu____18772 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____18775 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____18772, uu____18775)  in
            match uu____18763 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____18793),FStar_Syntax_Syntax.Total
                    (t2,uu____18795)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____18812 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____18812 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____18813,FStar_Syntax_Syntax.Total uu____18814) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____18832),FStar_Syntax_Syntax.Total
                    (t2,uu____18834)) ->
                     let uu____18851 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____18851 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____18853),FStar_Syntax_Syntax.GTotal
                    (t2,uu____18855)) ->
                     let uu____18872 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____18872 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____18874),FStar_Syntax_Syntax.GTotal
                    (t2,uu____18876)) ->
                     let uu____18893 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____18893 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____18894,FStar_Syntax_Syntax.Comp uu____18895) ->
                     let uu____18904 =
                       let uu___168_18907 = problem  in
                       let uu____18910 =
                         let uu____18911 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____18911
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___168_18907.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____18910;
                         FStar_TypeChecker_Common.relation =
                           (uu___168_18907.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___168_18907.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___168_18907.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___168_18907.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___168_18907.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___168_18907.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___168_18907.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___168_18907.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____18904 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____18912,FStar_Syntax_Syntax.Comp uu____18913) ->
                     let uu____18922 =
                       let uu___168_18925 = problem  in
                       let uu____18928 =
                         let uu____18929 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____18929
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___168_18925.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____18928;
                         FStar_TypeChecker_Common.relation =
                           (uu___168_18925.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___168_18925.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___168_18925.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___168_18925.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___168_18925.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___168_18925.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___168_18925.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___168_18925.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____18922 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____18930,FStar_Syntax_Syntax.GTotal uu____18931) ->
                     let uu____18940 =
                       let uu___169_18943 = problem  in
                       let uu____18946 =
                         let uu____18947 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____18947
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___169_18943.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___169_18943.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___169_18943.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____18946;
                         FStar_TypeChecker_Common.element =
                           (uu___169_18943.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___169_18943.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___169_18943.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___169_18943.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___169_18943.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___169_18943.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____18940 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____18948,FStar_Syntax_Syntax.Total uu____18949) ->
                     let uu____18958 =
                       let uu___169_18961 = problem  in
                       let uu____18964 =
                         let uu____18965 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____18965
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___169_18961.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___169_18961.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___169_18961.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____18964;
                         FStar_TypeChecker_Common.element =
                           (uu___169_18961.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___169_18961.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___169_18961.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___169_18961.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___169_18961.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___169_18961.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____18958 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____18966,FStar_Syntax_Syntax.Comp uu____18967) ->
                     let uu____18968 =
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
                     if uu____18968
                     then
                       let uu____18969 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____18969 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____18973 =
                            let uu____18978 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____18978
                            then (c1_comp, c2_comp)
                            else
                              (let uu____18984 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____18985 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____18984, uu____18985))
                             in
                          match uu____18973 with
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
                           (let uu____18992 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____18992
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____18994 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____18994 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____18997 =
                                  let uu____18998 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____18999 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____18998 uu____18999
                                   in
                                giveup env uu____18997 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____19006 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____19039  ->
              match uu____19039 with
              | (uu____19050,tm,uu____19052,uu____19053,uu____19054) ->
                  FStar_Syntax_Print.term_to_string tm))
       in
    FStar_All.pipe_right uu____19006 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____19087 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____19087 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____19105 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____19133  ->
                match uu____19133 with
                | (u1,u2) ->
                    let uu____19140 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____19141 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____19140 uu____19141))
         in
      FStar_All.pipe_right uu____19105 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____19168,[])) -> "{}"
      | uu____19193 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____19216 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____19216
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____19219 =
              FStar_List.map
                (fun uu____19229  ->
                   match uu____19229 with
                   | (uu____19234,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____19219 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____19239 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____19239 imps
  
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
                  let uu____19292 =
                    FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "ExplainRel")
                     in
                  if uu____19292
                  then
                    let uu____19293 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____19294 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____19293
                      (rel_to_string rel) uu____19294
                  else "TOP"  in
                let uu____19296 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____19296 with
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
              let uu____19353 =
                let uu____19356 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _0_27  -> FStar_Pervasives_Native.Some _0_27)
                  uu____19356
                 in
              FStar_Syntax_Syntax.new_bv uu____19353 t1  in
            let uu____19359 =
              let uu____19364 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____19364
               in
            match uu____19359 with | (p,wl1) -> (p, x, wl1)
  
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
          let uu____19420 = FStar_Options.eager_inference ()  in
          if uu____19420
          then
            let uu___170_19421 = probs  in
            {
              attempting = (uu___170_19421.attempting);
              wl_deferred = (uu___170_19421.wl_deferred);
              ctr = (uu___170_19421.ctr);
              defer_ok = false;
              smt_ok = (uu___170_19421.smt_ok);
              tcenv = (uu___170_19421.tcenv);
              wl_implicits = (uu___170_19421.wl_implicits)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success (deferred,implicits) ->
            (FStar_Syntax_Unionfind.commit tx;
             FStar_Pervasives_Native.Some (deferred, implicits))
        | Failed (d,s) ->
            ((let uu____19441 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____19441
              then
                let uu____19442 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____19442
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
          ((let uu____19464 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____19464
            then
              let uu____19465 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____19465
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops;
                FStar_TypeChecker_Normalize.NoFullNorm] env f
               in
            (let uu____19469 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____19469
             then
               let uu____19470 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____19470
             else ());
            (let f2 =
               let uu____19473 =
                 let uu____19474 = FStar_Syntax_Util.unmeta f1  in
                 uu____19474.FStar_Syntax_Syntax.n  in
               match uu____19473 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____19478 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___171_19479 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___171_19479.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___171_19479.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___171_19479.FStar_TypeChecker_Env.implicits)
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
            let uu____19593 =
              let uu____19594 =
                let uu____19595 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _0_28  -> FStar_TypeChecker_Common.NonTrivial _0_28)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____19595;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____19594  in
            FStar_All.pipe_left
              (fun _0_29  -> FStar_Pervasives_Native.Some _0_29) uu____19593
  
let with_guard_no_simp :
  'Auu____19610 .
    'Auu____19610 ->
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
            let uu____19633 =
              let uu____19634 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _0_30  -> FStar_TypeChecker_Common.NonTrivial _0_30)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____19634;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____19633
  
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
          (let uu____19674 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____19674
           then
             let uu____19675 = FStar_Syntax_Print.term_to_string t1  in
             let uu____19676 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____19675
               uu____19676
           else ());
          (let uu____19678 =
             let uu____19683 = empty_worklist env  in
             let uu____19684 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem uu____19683 env t1 FStar_TypeChecker_Common.EQ t2
               FStar_Pervasives_Native.None uu____19684
              in
           match uu____19678 with
           | (prob,wl) ->
               let g =
                 let uu____19692 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____19712  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____19692  in
               g)
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____19756 = try_teq true env t1 t2  in
        match uu____19756 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____19760 = FStar_TypeChecker_Env.get_range env  in
              let uu____19761 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____19760 uu____19761);
             trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____19768 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____19768
              then
                let uu____19769 = FStar_Syntax_Print.term_to_string t1  in
                let uu____19770 = FStar_Syntax_Print.term_to_string t2  in
                let uu____19771 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____19769
                  uu____19770 uu____19771
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
          let uu____19793 = FStar_TypeChecker_Env.get_range env  in
          let uu____19794 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____19793 uu____19794
  
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
        (let uu____19819 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____19819
         then
           let uu____19820 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____19821 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____19820 uu____19821
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____19824 =
           let uu____19831 = empty_worklist env  in
           let uu____19832 = FStar_TypeChecker_Env.get_range env  in
           new_problem uu____19831 env c1 rel c2 FStar_Pervasives_Native.None
             uu____19832 "sub_comp"
            in
         match uu____19824 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             let uu____19842 =
               solve_and_commit env (singleton wl prob1 true)
                 (fun uu____19862  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob1) uu____19842)
  
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
      fun uu____19917  ->
        match uu____19917 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____19960 =
                 let uu____19965 =
                   let uu____19966 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____19967 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____19966 uu____19967
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____19965)  in
               let uu____19968 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____19960 uu____19968)
               in
            let equiv1 v1 v' =
              let uu____19980 =
                let uu____19985 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____19986 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____19985, uu____19986)  in
              match uu____19980 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____20005 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____20035 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____20035 with
                      | FStar_Syntax_Syntax.U_unif uu____20042 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____20071  ->
                                    match uu____20071 with
                                    | (u,v') ->
                                        let uu____20080 = equiv1 v1 v'  in
                                        if uu____20080
                                        then
                                          let uu____20083 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____20083 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____20099 -> []))
               in
            let uu____20104 =
              let wl =
                let uu___172_20108 = empty_worklist env  in
                {
                  attempting = (uu___172_20108.attempting);
                  wl_deferred = (uu___172_20108.wl_deferred);
                  ctr = (uu___172_20108.ctr);
                  defer_ok = false;
                  smt_ok = (uu___172_20108.smt_ok);
                  tcenv = (uu___172_20108.tcenv);
                  wl_implicits = (uu___172_20108.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____20126  ->
                      match uu____20126 with
                      | (lb,v1) ->
                          let uu____20133 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____20133 with
                           | USolved wl1 -> ()
                           | uu____20135 -> fail1 lb v1)))
               in
            let rec check_ineq uu____20145 =
              match uu____20145 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____20154) -> true
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
                      uu____20177,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____20179,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____20190) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____20197,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____20205 -> false)
               in
            let uu____20210 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____20225  ->
                      match uu____20225 with
                      | (u,v1) ->
                          let uu____20232 = check_ineq (u, v1)  in
                          if uu____20232
                          then true
                          else
                            ((let uu____20235 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____20235
                              then
                                let uu____20236 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____20237 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____20236
                                  uu____20237
                              else ());
                             false)))
               in
            if uu____20210
            then ()
            else
              ((let uu____20241 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____20241
                then
                  ((let uu____20243 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____20243);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____20253 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____20253))
                else ());
               (let uu____20263 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____20263))
  
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
        let fail1 uu____20330 =
          match uu____20330 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___173_20351 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___173_20351.attempting);
            wl_deferred = (uu___173_20351.wl_deferred);
            ctr = (uu___173_20351.ctr);
            defer_ok;
            smt_ok = (uu___173_20351.smt_ok);
            tcenv = (uu___173_20351.tcenv);
            wl_implicits = (uu___173_20351.wl_implicits)
          }  in
        (let uu____20353 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____20353
         then
           let uu____20354 = FStar_Util.string_of_bool defer_ok  in
           let uu____20355 = wl_to_string wl  in
           let uu____20356 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____20354 uu____20355 uu____20356
         else ());
        (let g1 =
           let uu____20369 = solve_and_commit env wl fail1  in
           match uu____20369 with
           | FStar_Pervasives_Native.Some
               (uu____20376::uu____20377,uu____20378) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___174_20403 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___174_20403.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___174_20403.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____20414 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___175_20422 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___175_20422.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___175_20422.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___175_20422.FStar_TypeChecker_Env.implicits)
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
    let uu____20470 = FStar_ST.op_Bang last_proof_ns  in
    match uu____20470 with
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
            let uu___176_20593 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___176_20593.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___176_20593.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___176_20593.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____20594 =
            let uu____20595 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____20595  in
          if uu____20594
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____20603 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____20604 =
                       let uu____20605 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____20605
                        in
                     FStar_Errors.diag uu____20603 uu____20604)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____20609 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____20610 =
                        let uu____20611 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____20611
                         in
                      FStar_Errors.diag uu____20609 uu____20610)
                   else ();
                   (let uu____20614 = FStar_TypeChecker_Env.get_range env  in
                    def_check_closed_in_env uu____20614 "discharge_guard'"
                      env vc1);
                   (let uu____20615 = check_trivial vc1  in
                    match uu____20615 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____20622 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____20623 =
                                let uu____20624 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____20624
                                 in
                              FStar_Errors.diag uu____20622 uu____20623)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____20629 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____20630 =
                                let uu____20631 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____20631
                                 in
                              FStar_Errors.diag uu____20629 uu____20630)
                           else ();
                           (let vcs =
                              let uu____20642 = FStar_Options.use_tactics ()
                                 in
                              if uu____20642
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____20661  ->
                                     (let uu____20663 =
                                        FStar_Options.set_options
                                          FStar_Options.Set "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a238  -> ())
                                        uu____20663);
                                     (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                       env vc2)
                              else
                                (let uu____20665 =
                                   let uu____20672 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____20672)  in
                                 [uu____20665])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____20706  ->
                                    match uu____20706 with
                                    | (env1,goal,opts) ->
                                        let goal1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Normalize.Simplify;
                                            FStar_TypeChecker_Normalize.Primops]
                                            env1 goal
                                           in
                                        let uu____20717 = check_trivial goal1
                                           in
                                        (match uu____20717 with
                                         | FStar_TypeChecker_Common.Trivial 
                                             ->
                                             if debug1
                                             then
                                               FStar_Util.print_string
                                                 "Goal completely solved by tactic\n"
                                             else ()
                                         | FStar_TypeChecker_Common.NonTrivial
                                             goal2 ->
                                             (FStar_Options.push ();
                                              FStar_Options.set opts;
                                              maybe_update_proof_ns env1;
                                              if debug1
                                              then
                                                (let uu____20725 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____20726 =
                                                   let uu____20727 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2
                                                      in
                                                   let uu____20728 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____20727 uu____20728
                                                    in
                                                 FStar_Errors.diag
                                                   uu____20725 uu____20726)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____20731 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____20732 =
                                                   let uu____20733 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal2
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____20733
                                                    in
                                                 FStar_Errors.diag
                                                   uu____20731 uu____20732)
                                              else ();
                                              (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                use_env_range_msg env1 goal2;
                                              FStar_Options.pop ())))));
                           FStar_Pervasives_Native.Some ret_g)))))
  
let (discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____20747 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____20747 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____20754 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____20754
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____20765 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____20765 with
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
            let uu____20798 = FStar_Syntax_Util.head_and_args u  in
            match uu____20798 with
            | (hd1,uu____20814) ->
                let uu____20835 =
                  let uu____20836 = FStar_Syntax_Subst.compress u  in
                  uu____20836.FStar_Syntax_Syntax.n  in
                (match uu____20835 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____20839 -> true
                 | uu____20840 -> false)
             in
          let rec until_fixpoint acc implicits =
            let uu____20860 = acc  in
            match uu____20860 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____20922 = hd1  in
                     (match uu____20922 with
                      | (reason,tm,ctx_u,r,should_check) ->
                          if Prims.op_Negation should_check
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____20939 = unresolved tm  in
                             if uu____20939
                             then until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               (let env1 =
                                  let uu___177_20952 = env  in
                                  {
                                    FStar_TypeChecker_Env.solver =
                                      (uu___177_20952.FStar_TypeChecker_Env.solver);
                                    FStar_TypeChecker_Env.range =
                                      (uu___177_20952.FStar_TypeChecker_Env.range);
                                    FStar_TypeChecker_Env.curmodule =
                                      (uu___177_20952.FStar_TypeChecker_Env.curmodule);
                                    FStar_TypeChecker_Env.gamma =
                                      (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                    FStar_TypeChecker_Env.gamma_sig =
                                      (uu___177_20952.FStar_TypeChecker_Env.gamma_sig);
                                    FStar_TypeChecker_Env.gamma_cache =
                                      (uu___177_20952.FStar_TypeChecker_Env.gamma_cache);
                                    FStar_TypeChecker_Env.modules =
                                      (uu___177_20952.FStar_TypeChecker_Env.modules);
                                    FStar_TypeChecker_Env.expected_typ =
                                      (uu___177_20952.FStar_TypeChecker_Env.expected_typ);
                                    FStar_TypeChecker_Env.sigtab =
                                      (uu___177_20952.FStar_TypeChecker_Env.sigtab);
                                    FStar_TypeChecker_Env.is_pattern =
                                      (uu___177_20952.FStar_TypeChecker_Env.is_pattern);
                                    FStar_TypeChecker_Env.instantiate_imp =
                                      (uu___177_20952.FStar_TypeChecker_Env.instantiate_imp);
                                    FStar_TypeChecker_Env.effects =
                                      (uu___177_20952.FStar_TypeChecker_Env.effects);
                                    FStar_TypeChecker_Env.generalize =
                                      (uu___177_20952.FStar_TypeChecker_Env.generalize);
                                    FStar_TypeChecker_Env.letrecs =
                                      (uu___177_20952.FStar_TypeChecker_Env.letrecs);
                                    FStar_TypeChecker_Env.top_level =
                                      (uu___177_20952.FStar_TypeChecker_Env.top_level);
                                    FStar_TypeChecker_Env.check_uvars =
                                      (uu___177_20952.FStar_TypeChecker_Env.check_uvars);
                                    FStar_TypeChecker_Env.use_eq =
                                      (uu___177_20952.FStar_TypeChecker_Env.use_eq);
                                    FStar_TypeChecker_Env.is_iface =
                                      (uu___177_20952.FStar_TypeChecker_Env.is_iface);
                                    FStar_TypeChecker_Env.admit =
                                      (uu___177_20952.FStar_TypeChecker_Env.admit);
                                    FStar_TypeChecker_Env.lax =
                                      (uu___177_20952.FStar_TypeChecker_Env.lax);
                                    FStar_TypeChecker_Env.lax_universes =
                                      (uu___177_20952.FStar_TypeChecker_Env.lax_universes);
                                    FStar_TypeChecker_Env.failhard =
                                      (uu___177_20952.FStar_TypeChecker_Env.failhard);
                                    FStar_TypeChecker_Env.nosynth =
                                      (uu___177_20952.FStar_TypeChecker_Env.nosynth);
                                    FStar_TypeChecker_Env.tc_term =
                                      (uu___177_20952.FStar_TypeChecker_Env.tc_term);
                                    FStar_TypeChecker_Env.type_of =
                                      (uu___177_20952.FStar_TypeChecker_Env.type_of);
                                    FStar_TypeChecker_Env.universe_of =
                                      (uu___177_20952.FStar_TypeChecker_Env.universe_of);
                                    FStar_TypeChecker_Env.check_type_of =
                                      (uu___177_20952.FStar_TypeChecker_Env.check_type_of);
                                    FStar_TypeChecker_Env.use_bv_sorts =
                                      (uu___177_20952.FStar_TypeChecker_Env.use_bv_sorts);
                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                      =
                                      (uu___177_20952.FStar_TypeChecker_Env.qtbl_name_and_index);
                                    FStar_TypeChecker_Env.normalized_eff_names
                                      =
                                      (uu___177_20952.FStar_TypeChecker_Env.normalized_eff_names);
                                    FStar_TypeChecker_Env.proof_ns =
                                      (uu___177_20952.FStar_TypeChecker_Env.proof_ns);
                                    FStar_TypeChecker_Env.synth_hook =
                                      (uu___177_20952.FStar_TypeChecker_Env.synth_hook);
                                    FStar_TypeChecker_Env.splice =
                                      (uu___177_20952.FStar_TypeChecker_Env.splice);
                                    FStar_TypeChecker_Env.is_native_tactic =
                                      (uu___177_20952.FStar_TypeChecker_Env.is_native_tactic);
                                    FStar_TypeChecker_Env.identifier_info =
                                      (uu___177_20952.FStar_TypeChecker_Env.identifier_info);
                                    FStar_TypeChecker_Env.tc_hooks =
                                      (uu___177_20952.FStar_TypeChecker_Env.tc_hooks);
                                    FStar_TypeChecker_Env.dsenv =
                                      (uu___177_20952.FStar_TypeChecker_Env.dsenv);
                                    FStar_TypeChecker_Env.dep_graph =
                                      (uu___177_20952.FStar_TypeChecker_Env.dep_graph)
                                  }  in
                                let tm1 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    tm
                                   in
                                let env2 =
                                  if forcelax
                                  then
                                    let uu___178_20955 = env1  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___178_20955.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___178_20955.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___178_20955.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___178_20955.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___178_20955.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___178_20955.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___178_20955.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___178_20955.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___178_20955.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___178_20955.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___178_20955.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___178_20955.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___178_20955.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___178_20955.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___178_20955.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___178_20955.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___178_20955.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___178_20955.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___178_20955.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___178_20955.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___178_20955.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___178_20955.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___178_20955.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___178_20955.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___178_20955.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___178_20955.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___178_20955.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___178_20955.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___178_20955.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___178_20955.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___178_20955.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___178_20955.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___178_20955.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___178_20955.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___178_20955.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___178_20955.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.dep_graph =
                                        (uu___178_20955.FStar_TypeChecker_Env.dep_graph)
                                    }
                                  else env1  in
                                (let uu____20958 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "RelCheck")
                                    in
                                 if uu____20958
                                 then
                                   let uu____20959 =
                                     FStar_Syntax_Print.uvar_to_string
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                      in
                                   let uu____20960 =
                                     FStar_Syntax_Print.term_to_string tm1
                                      in
                                   let uu____20961 =
                                     FStar_Syntax_Print.term_to_string
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                      in
                                   let uu____20962 =
                                     FStar_Range.string_of_range r  in
                                   FStar_Util.print5
                                     "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                     uu____20959 uu____20960 uu____20961
                                     reason uu____20962
                                 else ());
                                (let g1 =
                                   try
                                     env2.FStar_TypeChecker_Env.check_type_of
                                       must_total env2 tm1
                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                   with
                                   | e ->
                                       ((let uu____20973 =
                                           let uu____20982 =
                                             let uu____20989 =
                                               let uu____20990 =
                                                 FStar_Syntax_Print.uvar_to_string
                                                   ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                  in
                                               let uu____20991 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env2 tm1
                                                  in
                                               FStar_Util.format2
                                                 "Failed while checking implicit %s set to %s"
                                                 uu____20990 uu____20991
                                                in
                                             (FStar_Errors.Error_BadImplicit,
                                               uu____20989, r)
                                              in
                                           [uu____20982]  in
                                         FStar_Errors.add_errors uu____20973);
                                        FStar_Exn.raise e)
                                    in
                                 let g2 =
                                   if env2.FStar_TypeChecker_Env.is_pattern
                                   then
                                     let uu___181_21005 = g1  in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___181_21005.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___181_21005.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___181_21005.FStar_TypeChecker_Env.implicits)
                                     }
                                   else g1  in
                                 let g' =
                                   let uu____21008 =
                                     discharge_guard'
                                       (FStar_Pervasives_Native.Some
                                          (fun uu____21015  ->
                                             FStar_Syntax_Print.term_to_string
                                               tm1)) env2 g2 true
                                      in
                                   match uu____21008 with
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
          let uu___182_21027 = g  in
          let uu____21028 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___182_21027.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___182_21027.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___182_21027.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____21028
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
        let uu____21082 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____21082 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____21093 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a239  -> ()) uu____21093
      | (reason,e,ctx_u,r,should_check)::uu____21099 ->
          let uu____21122 =
            let uu____21127 =
              let uu____21128 =
                FStar_Syntax_Print.uvar_to_string
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____21129 =
                FStar_TypeChecker_Normalize.term_to_string env
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              let uu____21130 = FStar_Util.string_of_bool should_check  in
              FStar_Util.format4
                "Failed to resolve implicit argument %s of type %s introduced for %s (should check=%s)"
                uu____21128 uu____21129 reason uu____21130
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____21127)
             in
          FStar_Errors.raise_error uu____21122 r
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___183_21141 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___183_21141.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___183_21141.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___183_21141.FStar_TypeChecker_Env.implicits)
      }
  
let (discharge_guard_nosmt :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.bool) =
  fun env  ->
    fun g  ->
      let uu____21156 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____21156 with
      | FStar_Pervasives_Native.Some uu____21162 -> true
      | FStar_Pervasives_Native.None  -> false
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21178 = try_teq false env t1 t2  in
        match uu____21178 with
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
        (let uu____21212 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____21212
         then
           let uu____21213 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____21214 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____21213
             uu____21214
         else ());
        (let uu____21216 =
           let uu____21223 = empty_worklist env  in
           new_t_prob uu____21223 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____21216 with
         | (prob,x,wl) ->
             let g =
               let uu____21236 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____21256  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____21236  in
             ((let uu____21286 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____21286
               then
                 let uu____21287 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____21288 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____21289 =
                   let uu____21290 = FStar_Util.must g  in
                   guard_to_string env uu____21290  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____21287 uu____21288 uu____21289
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
        let uu____21324 = check_subtyping env t1 t2  in
        match uu____21324 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____21343 =
              let uu____21344 = FStar_Syntax_Syntax.mk_binder x  in
              abstract_guard uu____21344 g  in
            FStar_Pervasives_Native.Some uu____21343
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____21362 = check_subtyping env t1 t2  in
        match uu____21362 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____21381 =
              let uu____21382 =
                let uu____21383 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____21383]  in
              close_guard env uu____21382 g  in
            FStar_Pervasives_Native.Some uu____21381
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____21412 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____21412
         then
           let uu____21413 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____21414 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____21413
             uu____21414
         else ());
        (let uu____21416 =
           let uu____21423 = empty_worklist env  in
           new_t_prob uu____21423 env t1 FStar_TypeChecker_Common.SUB t2  in
         match uu____21416 with
         | (prob,x,wl) ->
             let g =
               let uu____21430 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____21450  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____21430  in
             (match g with
              | FStar_Pervasives_Native.None  -> false
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____21481 =
                      let uu____21482 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____21482]  in
                    close_guard env uu____21481 g1  in
                  discharge_guard_nosmt env g2))
  